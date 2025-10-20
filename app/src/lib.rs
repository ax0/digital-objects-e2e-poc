#![allow(clippy::uninlined_format_args)]

use std::collections::HashSet;

use anyhow::{Context, Result};
use pod2::{
    frontend::{MainPodBuilder, Operation},
    lang::parse,
    middleware::{
        CustomPredicateRef, EMPTY_VALUE, Hash, Key, Params, Statement, TypedValue, Value,
        containers::{Dictionary, Set},
    },
};
use serde::{Deserialize, Serialize};

pub const DEPTH: usize = 32;

pub const IDS_STR: &str = "ids";
pub const NULLIFIERS_STR: &str = "nullifiers";

pub type Id = Hash;

#[macro_export]
macro_rules! dict {
    ({ $($key:expr => $val:expr),* , }) => (
        $crate::dict!({ $($key => $val),* }).unwrap()
    );
    ({ $($key:expr => $val:expr),* }) => ({
        pod2::dict!(DEPTH, { $($key => $val),* }).unwrap()
    });
}

#[derive(Debug, Clone)]
pub struct Predicates {
    pub init: CustomPredicateRef,
    pub append: CustomPredicateRef,
    pub nullify: CustomPredicateRef,
    pub update: CustomPredicateRef,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Op {
    Init,
    Append { id: Id /* TODO: POD */ },
    Nullify { id: Id /* TODO: POD */ },
}

impl From<Op> for Dictionary {
    fn from(op: Op) -> Self {
        match op {
            Op::Init => dict!({"name" => "init"}),
            Op::Append { id } => {
                dict!({"name" => "append", "id" => id})
            }
            Op::Nullify { id } => {
                dict!({"name" => "nullify", "id" => id})
            }
        }
    }
}

/// "...we store two lists, one for the IDs of all created items, and one for the nullifiers of all destroyed ones"
/// State = Dict {
///   "ids" => Set(...),
///   "nullifiers" => Set(...)
/// }
pub fn build_predicates(params: &Params) -> Predicates {
    let empty = format!("Raw({:#})", EMPTY_VALUE);
    let empty_state = format!(r#"{{"{IDS_STR}": {empty}, "{NULLIFIERS_STR}": {empty}}}"#);

    let input_state = format!(
        r#"
        // State predicates
        init(new, old, op) = AND(
            // Input validation
            DictContains(op, "name", "init")
            // State transition
            Equal(old, {empty})
            Equal(new, {empty_state})
        )

        append(new, old, op, private: old_set, new_set) = AND(
            // Input validation
            DictContains(op, "name", "append")
            // State transition
            DictContains(old, "{IDS_STR}", old_set)
            SetInsert(new_set, old_set, op.id)
            DictUpdate(new, old, "{IDS_STR}", new_set)
        )

        nullify(new, old, op, private: old_set, new_set) = AND(
            // Input validation
            DictContains(op, "name", "nullify")
            // TODO: Check existence of ID before nullifying
            // DictContains(old, "{IDS_STR}", old_id_set)
            // SetContains(old_id_set, op.id)
            // State transition
            DictContains(old, "{NULLIFIERS_STR}", old_set)
            SetInsert(new_set, old_set, op.id)
            DictUpdate(new, old, "{NULLIFIERS_STR}", new_set)
        )

        update(new, old, op) = OR(
            init(new, old, op)
            append(new, old, op)
            nullify(new, old, op)
        )
    "#
    );

    let state_batch = parse(&input_state, params, &[]).unwrap().custom_batch;

    // State batch predicates

    Predicates {
        init: state_batch.predicate_ref_by_name("init").unwrap(),
        append: state_batch.predicate_ref_by_name("append").unwrap(),
        nullify: state_batch.predicate_ref_by_name("nullify").unwrap(),
        update: state_batch.predicate_ref_by_name("update").unwrap(),
    }
}

pub struct Helper<'a> {
    pub builder: &'a mut MainPodBuilder,
    pub predicates: &'a Predicates,
}

impl<'a> Helper<'a> {
    pub fn new(pod_builder: &'a mut MainPodBuilder, predicates: &'a Predicates) -> Self {
        Self {
            builder: pod_builder,
            predicates,
        }
    }

    pub fn st_init(&mut self, old: Dictionary, op: Dictionary) -> Result<(Dictionary, Statement)> {
        let name = String::try_from(op.get(&Key::from("name")).unwrap().typed()).unwrap();
        assert_eq!(name, "init");
        // DictContains(op, "name", "init")
        let st0 = self
            .builder
            .priv_op(Operation::dict_contains(op.clone(), "name", "init"))
            .unwrap();
        // Equal(old, EMPTY)
        let st1 = self
            .builder
            .priv_op(Operation::eq(old.clone(), EMPTY_VALUE))
            .context("old state is not empty")?;

        let empty_group = Value::from(Set::new(DEPTH, HashSet::new()).unwrap());
        let init_state = dict!({
            IDS_STR => empty_group.clone(),
            NULLIFIERS_STR => empty_group.clone()
        }
        );
        // Equal(new, {"ids": EMPTY, "nullifiers": EMPTY})
        let st2 = self
            .builder
            .priv_op(Operation::eq(init_state.clone(), init_state.clone()))
            .unwrap();

        // init(new, old, op)
        let st = self
            .builder
            .priv_op(Operation::custom(
                self.predicates.init.clone(),
                [st0, st1, st2],
            ))
            .unwrap();
        Ok((init_state, st))
    }

    pub fn st_append_nullify(
        &mut self,
        old: Dictionary,
        op: Dictionary,
    ) -> Result<(Dictionary, Statement)> {
        let name = String::try_from(op.get(&Key::from("name")).unwrap().typed()).unwrap();
        assert!(name == "append" || name == "nullify");

        let set_name = if name == "append" {
            IDS_STR
        } else {
            NULLIFIERS_STR
        };

        let st0 = if name == "append" {
            // DictContains(op, "name", "append")
            self.builder
                .priv_op(Operation::dict_contains(op.clone(), "name", "append"))
                .unwrap()
        } else {
            // DictContains(op, "name", "nullify")
            self.builder
                .priv_op(Operation::dict_contains(op.clone(), "name", "nullify"))
                .unwrap()
        };

        let old_set = old.get(&set_name.into()).unwrap();

        // DictContains(old, set_name, old_set)
        let st1 = self
            .builder
            .priv_op(Operation::dict_contains(
                old.clone(),
                set_name,
                old_set.clone(),
            ))
            .unwrap();

        let id = op.get(&Key::from("id")).unwrap();
        let mut new_set = if let TypedValue::Set(set) = old_set.typed() {
            set.clone()
        } else {
            panic!("Value not a Set: {:?}", old_set)
        };
        let st2 = {
            new_set.insert(id).unwrap();
            // SetInsert(new_set, old_set, op.id)
            self.builder
                .priv_op(Operation::set_insert(
                    new_set.clone(),
                    old_set.clone(),
                    (&op, "id"),
                ))
                .context("old_set already contains id")?
        };

        let mut new = old.clone();
        new.update(&Key::from(set_name), &Value::from(new_set.clone()))
            .unwrap();
        // DictUpdate(new, old, set_name, new_set)
        let st3 = self
            .builder
            .priv_op(Operation::dict_update(
                new.clone(),
                old.clone(),
                set_name,
                new_set,
            ))
            .unwrap();

        let st = if name == "append" {
            // add(new, old, op, private: old_set, new_set)
            self.builder
                .priv_op(Operation::custom(
                    self.predicates.append.clone(),
                    [st0, st1, st2, st3],
                ))
                .unwrap()
        } else {
            // let id_set = Key::try_from(op.get(&Key::from(IDS_STR)).unwrap().typed()).unwrap();
            // let old_id_set = old.get(&id_set).unwrap();

            // // DictContains(old, IDS_STR, old_id_set)
            // let id_check_st0 = self
            //     .builder
            //     .priv_op(Operation::dict_contains(
            //         old.clone(),
            //         IDS_STR,
            //         old_id_set.clone(),
            //     ))
            //     .unwrap();

            // // SetContains(old_id_set, op.id)
            // let id_check_st1 = self
            //     .builder
            //     .priv_op(Operation::set_contains(
            //         old_id_set,
            //         (&op, IDS_STR)
            //     ))
            //     .unwrap();

            // del(new, old, op, private: old_id_set, old_set, new_set)
            self.builder
                .priv_op(Operation::custom(
                    self.predicates.nullify.clone(),
                    [st0, /* id_check_st0, id_check_st1, */ st1, st2, st3],
                ))
                .unwrap()
        };
        Ok((new, st))
    }

    pub fn st_update(
        &mut self,
        old: Dictionary,
        op: Dictionary,
    ) -> Result<(Dictionary, Statement)> {
        let name = String::try_from(op.get(&Key::from("name")).unwrap().typed()).unwrap();
        let st_none = Statement::None;
        let (new, sts) = match name.as_str() {
            "init" => {
                // init(new, old, op)
                let (new, st) = self.st_init(old, op)?;
                (new, [st, st_none.clone(), st_none.clone()])
            }
            "append" => {
                // append(new, old, op, private: old_set, new_set)
                let (new, st) = self.st_append_nullify(old, op)?;
                (new, [st_none.clone(), st, st_none.clone()])
            }
            "nullify" => {
                // nullify(new, old, op, private: old_id_set, old_set, new_set)
                let (new, st) = self.st_append_nullify(old, op)?;
                (new, [st_none.clone(), st_none.clone(), st])
            }
            _ => panic!("invalid op.name = {}", name),
        };

        // TODO: Verify provided POD.

        // update(new, old, op)
        let st = self
            .builder
            .priv_op(Operation::custom(self.predicates.update.clone(), sts))
            .unwrap();
        Ok((new, st))
    }
}

#[cfg(test)]
mod tests {
    use pod2::{
        backends::plonky2::mainpod::Prover,
        frontend::MainPodBuilder,
        lang::PrettyPrint,
        middleware::{DEFAULT_VD_SET, MainPodProver, Params, VDSet, hash_str},
    };

    use super::*;

    #[allow(clippy::too_many_arguments)]
    fn update(
        params: &Params,
        vd_set: &VDSet,
        prover: &dyn MainPodProver,
        predicates: &Predicates,
        state: Dictionary,
        op: Op,
    ) -> Dictionary {
        let mut builder = MainPodBuilder::new(params, vd_set);
        let mut helper = Helper::new(&mut builder, predicates);

        // State Pod
        let (state, st_update) = helper
            .st_update(state, Dictionary::from(op.clone()))
            .unwrap();
        builder.reveal(&st_update);

        let state_pod = builder.prove(prover).unwrap();
        println!("# state_pod\n:{}", state_pod);
        println!(
            "# state\n:{}",
            Value::from(state.clone()).to_podlang_string()
        );
        state_pod.pod.verify().unwrap();

        state
    }

    #[test]
    fn test_app() {
        env_logger::init();
        // let (vd_set, prover) = (&VDSet::new(8, &[]).unwrap(), &MockProver {});
        let (vd_set, prover) = (&*DEFAULT_VD_SET, &Prover {});

        let params = Params::default();
        let state_predicates = build_predicates(&params);

        // Initial state
        let mut state = dict!({});
        println!(
            "# state\n:{}",
            Value::from(state.clone()).to_podlang_string()
        );
        for op in [
            Op::Init,
            Op::Append { id: hash_str("33") },
            Op::Nullify { id: hash_str("33") },
        ] {
            state = update(&params, vd_set, prover, &state_predicates, state, op);
        }
    }
}
