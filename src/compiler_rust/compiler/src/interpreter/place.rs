//! Place (lvalue) model for the interpreter.
//!
//! Before this module the interpreter had no general notion of a *place*. Field
//! assignment was hand-written for exactly two levels (`a.b = v`, `a.b.c = v`)
//! and rejected anything deeper with
//! "deeply nested field access requires intermediate variables"; the
//! method-call receiver path had the same two-level ceiling but **no guard**, so
//! `a.b.c.mutate()` silently evaluated the receiver to a copy, mutated the copy
//! and dropped the write. The loud error and the silent loss were the same
//! unsupported place spelled two different ways.
//!
//! A place here is an environment-rooted variable plus an arbitrary chain of
//! field / index projections. `resolve_place` turns an lvalue expression into
//! that path, `write_place` performs the write-through, and both the assignment
//! statement path and the mutating-method receiver path route through them.
//!
//! ## Value semantics are preserved
//!
//! Interpreter values are `Arc`-based copy-on-write (`Value::Object { fields:
//! Arc<HashMap<..>> }`, `Value::Array(Arc<Vec<..>>)`), and this module walks
//! them with `Arc::make_mut`. A uniquely-owned container is mutated in place; a
//! genuinely aliased one deep-copies first. That is exactly the existing COW
//! contract — arrays stay value types, no aliasing is introduced. The change is
//! *reach* (arbitrary depth) and *coverage* (receivers as well as assignment),
//! not semantics.
//!
//! Expressions that are not places (temporaries, call results, literals) return
//! `None` and callers keep their previous copy behavior.

use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{ClassDef, Expr, FunctionDef};

use super::core_types::{Enums, ImplMethods};
use super::expr::evaluate_expr;
use super::interpreter_state::MODULE_GLOBALS;
use crate::error::CompileError;
use crate::value::{Env, Value};

/// One projection step along an lvalue path.
#[derive(Debug, Clone)]
pub(crate) enum Projection {
    /// `.name` — struct/class field, or a string-keyed dict entry.
    Field(String),
    /// `[expr]` — the index/key already evaluated to a value.
    Index(Value),
}

/// A resolved lvalue: a variable slot in `env` plus the projections that lead
/// from it to the target storage.
#[derive(Debug, Clone)]
pub(crate) struct Place {
    /// Name of the root variable in the environment.
    pub root: String,
    /// Projections applied to the root, outermost first.
    pub projections: Vec<Projection>,
}

/// Resolve `expr` to a place, or `None` when it is not one.
///
/// The root must be an identifier that is currently bound in `env` (a module
/// global promoted into `env` counts). Anything else — a call result, a
/// literal, a bare module name used for namespacing — is a temporary and is
/// deliberately not a place.
///
/// Index expressions are evaluated here (once), so a caller that both reads and
/// writes through the place never double-evaluates a side-effecting index.
pub(crate) fn resolve_place(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Place>, CompileError> {
    match expr {
        Expr::Identifier(name) => {
            if env.contains_key(name) {
                Ok(Some(Place {
                    root: name.clone(),
                    projections: Vec::new(),
                }))
            } else {
                // Not a bound variable: a module name, a type name, or an
                // undefined identifier. Not a place.
                Ok(None)
            }
        }
        Expr::FieldAccess { receiver, field } => {
            match resolve_place(receiver, env, functions, classes, enums, impl_methods)? {
                Some(mut place) => {
                    place.projections.push(Projection::Field(field.clone()));
                    Ok(Some(place))
                }
                None => Ok(None),
            }
        }
        Expr::Index { receiver, index } => {
            match resolve_place(receiver, env, functions, classes, enums, impl_methods)? {
                Some(mut place) => {
                    let index_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
                    place.projections.push(Projection::Index(index_val));
                    Ok(Some(place))
                }
                None => Ok(None),
            }
        }
        // `m!.n = 44`: `!` on an optional class/struct is the identity on the
        // value (it only narrows `T?` to `T`), so the unwrapped object is the
        // SAME place as the wrapped one and must be writable through. Without
        // this arm the interpreter rejected the shape with
        // `field assignment target is not a place` while the JIT accepted it —
        // an engine divergence.
        // Bug: doc/08_tracking/bug/jit_optional_class_unwrap_field_access_segv_2026-08-20.md
        Expr::ForceUnwrap(inner) => resolve_place(inner, env, functions, classes, enums, impl_methods),
        _ => Ok(None),
    }
}

/// Normalize a possibly-negative index against a container length.
fn normalize_index(len: usize, index: &Value) -> Option<usize> {
    let raw = match index {
        Value::Int(i) => *i,
        Value::UInt { value, .. } => *value as i64,
        _ => return None,
    };
    let resolved = if raw < 0 { len as i64 + raw } else { raw };
    if resolved < 0 || resolved as usize >= len {
        return None;
    }
    Some(resolved as usize)
}

fn value_as_u8(value: &Value) -> Option<u8> {
    match value {
        Value::UInt { value, .. } => u8::try_from(*value).ok(),
        Value::Int(value) => u8::try_from(*value).ok(),
        _ => None,
    }
}

/// Take one projection step, yielding a mutable reference to the projected
/// storage. `Arc::make_mut` keeps copy-on-write semantics: unique containers
/// mutate in place, shared ones deep-copy first.
fn step_mut<'a>(slot: &'a mut Value, projection: &Projection) -> Option<&'a mut Value> {
    match (slot, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => Arc::make_mut(fields).get_mut(name),
        (Value::Dict(entries), Projection::Field(name)) => Arc::make_mut(entries).get_mut(name),
        (Value::Array(items), Projection::Index(index)) => {
            let idx = normalize_index(items.len(), index)?;
            Arc::make_mut(items).get_mut(idx)
        }
        (Value::FixedSizeArray { data, .. }, Projection::Index(index)) => {
            let idx = normalize_index(data.len(), index)?;
            data.get_mut(idx)
        }
        (Value::Tuple(items), Projection::Index(index)) => {
            let idx = normalize_index(items.len(), index)?;
            items.get_mut(idx)
        }
        (Value::Dict(entries), Projection::Index(key)) => {
            // Composite dict keys are stored wrapped by `Value::wrap_dict_entry`
            // (a marker tuple). Projecting through that wrapper is not modelled
            // here, so only scalar keys are treated as places.
            if !key.dict_key_is_scalar() {
                return None;
            }
            let key_string = key.to_key_string();
            Arc::make_mut(entries).get_mut(&key_string)
        }
        _ => None,
    }
}

/// Walk every projection, returning a mutable reference to the final storage.
fn project_mut<'a>(root: &'a mut Value, projections: &[Projection]) -> Option<&'a mut Value> {
    let mut slot = root;
    for projection in projections {
        slot = step_mut(slot, projection)?;
    }
    Some(slot)
}

/// Store `value` at the final projection of `container`.
///
/// The last step is an *insert*, not a navigation: assigning a field that does
/// not exist yet creates it, matching what the existing one- and two-level
/// field-assignment paths do with `HashMap::insert`.
fn store_last(container: &mut Value, projection: &Projection, value: Value) -> bool {
    match (container, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => {
            Arc::make_mut(fields).insert(name.clone(), value);
            true
        }
        (Value::Dict(entries), Projection::Field(name)) => {
            Arc::make_mut(entries).insert(name.clone(), value);
            true
        }
        (Value::Array(items), Projection::Index(index)) => match normalize_index(items.len(), index) {
            Some(idx) => {
                Arc::make_mut(items)[idx] = value;
                true
            }
            None => false,
        },
        (slot @ Value::ByteArray(_), Projection::Index(index)) => {
            let Value::ByteArray(bytes) = slot else { unreachable!() };
            let Some(idx) = normalize_index(bytes.len(), index) else {
                return false;
            };
            if let Some(byte) = value_as_u8(&value) {
                Arc::make_mut(bytes)[idx] = byte;
            } else {
                let mut widened = Value::byte_array_values(bytes);
                widened[idx] = value;
                *slot = Value::array(widened);
            }
            true
        }
        (Value::FixedSizeArray { data, .. }, Projection::Index(index)) => match normalize_index(data.len(), index) {
            Some(idx) => {
                data[idx] = value;
                true
            }
            None => false,
        },
        (Value::Tuple(items), Projection::Index(index)) => match normalize_index(items.len(), index) {
            Some(idx) => {
                items[idx] = value;
                true
            }
            None => false,
        },
        (Value::Dict(entries), Projection::Index(key)) => {
            if !key.dict_key_is_scalar() {
                return false;
            }
            Arc::make_mut(entries).insert(key.to_key_string(), value);
            true
        }
        _ => false,
    }
}

/// Write `value` through `place`.
///
/// Returns `true` when the write landed, `false` when the path does not resolve
/// to real storage (a missing intermediate field, an out-of-bounds index, a
/// scalar where a container was expected). Callers treat `false` as "not a
/// place after all" and fall back to their previous behavior rather than
/// erroring, so this never turns a previously-working program into a failure.
pub(crate) fn write_place(env: &mut Env, place: &Place, value: Value) -> bool {
    let Some((last, parents)) = place.projections.split_last() else {
        // No projections: a bare variable write.
        env.insert(place.root.clone(), value);
        sync_module_global(env, &place.root);
        return true;
    };
    let Some(root_slot) = env.get_mut(&place.root) else {
        return false;
    };
    let Some(container) = project_mut(root_slot, parents) else {
        return false;
    };
    if !store_last(container, last, value) {
        return false;
    }
    sync_module_global(env, &place.root);
    true
}

/// Mirror a mutated root back into MODULE_GLOBALS when it is a module-level
/// binding, matching what the identifier and two-level paths already do.
fn sync_module_global(env: &Env, root: &str) {
    MODULE_GLOBALS.with(|cell| {
        // Peek before the write borrow: borrow_mut() on this generation-tracked
        // cell invalidates every owned-env template (2026-08-21 stall record).
        if !cell.borrow().contains_key(root) {
            return;
        }
        let mut globals = cell.borrow_mut();
        {
            if let Some(updated) = env.get(root) {
                globals.insert(root.to_string(), updated.clone());
            }
        }
    });
}

/// Produce an updated copy of the place's ROOT value with `value` stored at the
/// place, without touching `env`.
///
/// Some call sites (the statement-position method-call path) do not write the
/// environment themselves — they return a `(variable, new_value)` update for
/// their caller to apply. This gives them the same arbitrary-depth write-through
/// in that shape.
pub(crate) fn updated_root(env: &Env, place: &Place, value: Value) -> Option<Value> {
    let mut root = env.get(&place.root)?.clone();
    let (last, parents) = place.projections.split_last()?;
    let container = project_mut(&mut root, parents)?;
    if !store_last(container, last, value) {
        return None;
    }
    Some(root)
}

/// Read-only counterpart of `step_mut`.
fn step_ref<'a>(slot: &'a Value, projection: &Projection) -> Option<&'a Value> {
    match (slot, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => fields.get(name),
        (Value::Dict(entries), Projection::Field(name)) => entries.get(name),
        (Value::Array(items), Projection::Index(index)) => items.get(normalize_index(items.len(), index)?),
        (Value::FixedSizeArray { data, .. }, Projection::Index(index)) => {
            data.get(normalize_index(data.len(), index)?)
        }
        (Value::Tuple(items), Projection::Index(index)) => items.get(normalize_index(items.len(), index)?),
        (Value::Dict(entries), Projection::Index(key)) => {
            if !key.dict_key_is_scalar() {
                return None;
            }
            entries.get(&key.to_key_string())
        }
        _ => None,
    }
}

/// True when the place currently resolves to real storage, i.e. a write through
/// it would land. Used to decide whether a method receiver is a real place
/// before committing to the place-based call path.
///
/// Deliberately read-only: it must not promote the root out of the shared
/// environment base just to answer a question.
pub(crate) fn place_is_live(env: &Env, place: &Place) -> bool {
    let Some(mut slot) = env.get(&place.root) else {
        return false;
    };
    // The final projection is an insert target, so it need not exist yet; every
    // intermediate hop must.
    let Some((_, parents)) = place.projections.split_last() else {
        return true;
    };
    for projection in parents {
        match step_ref(slot, projection) {
            Some(next) => slot = next,
            None => return false,
        }
    }
    // The leaf must exist for a receiver read to make sense.
    step_ref(slot, place.projections.last().expect("checked non-empty")).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn object(class: &str, fields: Vec<(&str, Value)>) -> Value {
        Value::Object {
            class: class.to_string(),
            fields: Arc::new(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect()),
        }
    }

    fn read(env: &Env, root: &str, path: &[&str]) -> Value {
        let mut current = env.get(root).unwrap().clone();
        for field in path {
            current = match current {
                Value::Object { fields, .. } => fields.get(*field).unwrap().clone(),
                other => panic!("not an object: {:?}", other),
            };
        }
        current
    }

    #[test]
    fn writes_through_three_field_hops() {
        let inner = object("Inner", vec![("n", Value::Int(0))]);
        let mid = object("Mid", vec![("inner", inner)]);
        let root = object("Root", vec![("mid", mid)]);

        let mut env = Env::new();
        env.insert("root".into(), root);

        let place = Place {
            root: "root".into(),
            projections: vec![
                Projection::Field("mid".into()),
                Projection::Field("inner".into()),
                Projection::Field("n".into()),
            ],
        };
        assert!(write_place(&mut env, &place, Value::Int(7)));
        assert_eq!(read(&env, "root", &["mid", "inner", "n"]), Value::Int(7));
    }

    #[test]
    fn write_through_alias_does_not_leak_into_the_copy() {
        // Value semantics: a separate binding taken before the write keeps the
        // old contents (Arc COW), it does not observe the mutation.
        let inner = object("Inner", vec![("n", Value::Int(0))]);
        let mid = object("Mid", vec![("inner", inner)]);
        let root = object("Root", vec![("mid", mid)]);

        let mut env = Env::new();
        env.insert("root".into(), root);
        let snapshot = env.get("root").unwrap().clone();
        env.insert("copy".into(), snapshot);

        let place = Place {
            root: "root".into(),
            projections: vec![
                Projection::Field("mid".into()),
                Projection::Field("inner".into()),
                Projection::Field("n".into()),
            ],
        };
        assert!(write_place(&mut env, &place, Value::Int(42)));

        assert_eq!(read(&env, "root", &["mid", "inner", "n"]), Value::Int(42));
        assert_eq!(read(&env, "copy", &["mid", "inner", "n"]), Value::Int(0));
    }

    #[test]
    fn write_through_array_element_field() {
        let elem = object("Elem", vec![("n", Value::Int(1))]);
        let holder = object("Holder", vec![("items", Value::Array(Arc::new(vec![elem])))]);

        let mut env = Env::new();
        env.insert("h".into(), holder);

        let place = Place {
            root: "h".into(),
            projections: vec![
                Projection::Field("items".into()),
                Projection::Index(Value::Int(0)),
                Projection::Field("n".into()),
            ],
        };
        assert!(write_place(&mut env, &place, Value::Int(99)));

        let items = match env.get("h").unwrap() {
            Value::Object { fields, .. } => fields.get("items").unwrap().clone(),
            other => panic!("not an object: {:?}", other),
        };
        match items {
            Value::Array(values) => match &values[0] {
                Value::Object { fields, .. } => assert_eq!(fields.get("n").unwrap().clone(), Value::Int(99)),
                other => panic!("not an object: {:?}", other),
            },
            other => panic!("not an array: {:?}", other),
        }
    }

    #[test]
    fn missing_field_reports_not_live_instead_of_erroring() {
        let root = object("Root", vec![("mid", Value::Int(0))]);
        let mut env = Env::new();
        env.insert("root".into(), root);

        let place = Place {
            root: "root".into(),
            projections: vec![
                Projection::Field("mid".into()),
                Projection::Field("inner".into()),
            ],
        };
        assert!(!place_is_live(&env, &place));
        assert!(!write_place(&mut env, &place, Value::Int(1)));
    }

    #[test]
    fn out_of_bounds_index_is_not_a_live_place() {
        let holder = object("Holder", vec![("items", Value::Array(Arc::new(vec![Value::Int(1)])))]);
        let mut env = Env::new();
        env.insert("h".into(), holder);

        let place = Place {
            root: "h".into(),
            projections: vec![Projection::Field("items".into()), Projection::Index(Value::Int(5))],
        };
        assert!(!place_is_live(&env, &place));
    }

    #[test]
    fn packed_byte_index_write_is_cow_and_non_byte_assignment_widens() {
        let mut env = Env::new();
        env.insert("bytes".into(), Value::byte_array(vec![1, 2]));
        env.insert("alias".into(), env.get("bytes").unwrap().clone());
        let first = Place {
            root: "bytes".into(),
            projections: vec![Projection::Index(Value::Int(0))],
        };
        assert!(write_place(&mut env, &first, Value::UInt { value: 9, width: 8 }));
        assert_eq!(env.get("bytes").unwrap().byte_array_view(), Some([9, 2].as_slice()));
        assert_eq!(env.get("alias").unwrap().byte_array_view(), Some([1, 2].as_slice()));

        let second = Place {
            root: "bytes".into(),
            projections: vec![Projection::Index(Value::Int(1))],
        };
        assert!(write_place(&mut env, &second, Value::text("not a byte")));
        assert!(matches!(env.get("bytes"), Some(Value::Array(_))));
    }
}
