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
//! field / index / unwrap projections. `resolve_place` turns an lvalue expression into
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
use std::sync::{Arc, Mutex};

use simple_parser::ast::{ClassDef, Expr, FunctionDef};

use super::core_types::{Enums, ImplMethods};
use super::expr::evaluate_expr;
use super::interpreter_state::MODULE_GLOBALS;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, SpecialEnumKind, SpecialEnumType, Value};

/// One projection step along an lvalue path.
#[derive(Debug, Clone)]
pub(crate) enum Projection {
    /// `.name` — struct/class field, or a string-keyed dict entry.
    Field(String),
    /// `[expr]` — the index/key already evaluated to a value.
    Index(Value),
    /// `!` — preserve the writable payload of Some/Ok, or a direct nullable value.
    Unwrap,
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

/// Frame key recording that parameter `name` is a borrow. Holds the
/// `Value::BorrowMut` it was bound from, or `Nil` for a bare argument to a
/// parameter declared `&mut T`. The NUL keeps it out of the user's namespace.
pub(crate) fn borrow_param_marker(name: &str) -> String {
    format!("\0borrow:{name}")
}

/// True when `expr` is an lvalue with an index in it, whose re-evaluation could
/// run user code or see a changed variable.
pub(crate) fn place_has_index(expr: &Expr) -> bool {
    match expr {
        Expr::Index { .. } => true,
        Expr::FieldAccess { receiver, .. } => place_has_index(receiver),
        Expr::ForceUnwrap(inner) => place_has_index(inner),
        _ => false,
    }
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
        // An implicit nullable object is its own place, but explicit Some/Ok
        // has a payload slot. Keep the unwrap in the path so both forms write
        // through the same storage that expression evaluation reads.
        Expr::ForceUnwrap(inner) => {
            match resolve_place(inner, env, functions, classes, enums, impl_methods)? {
                Some(mut place) => {
                    place.projections.push(Projection::Unwrap);
                    Ok(Some(place))
                }
                None => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

const CALL_ROOT_BINDING: &str = "\u{0}place_call_root";

/// Refuse a write through a call-result root (bound by [`bind_call_root`])
/// when it would land in a copy and be lost. This engine's arrays, dicts,
/// byte arrays and structs are copy-on-write `Arc` values; pure-Simple and the
/// seed JIT treat them as shared handles and write through. If any container
/// on the path from the bound root to the written slot is still held elsewhere
/// (refcount > 1; the bound root itself counts only its own binding), the
/// write cannot reach that storage here, so it is refused rather than dropped.
/// A path through a `ClassInstance` stops the walk: the instance is shared and
/// the write lands in it. Places not rooted at a call result pass untouched.
/// Bug: doc/08_tracking/bug/seed_interp_call_root_shared_write_dropped_2026-11-07.md
pub(crate) fn refuse_shared_call_root(env: &Env, place: &Place) -> Result<(), CompileError> {
    if place.root != CALL_ROOT_BINDING {
        return Ok(());
    }
    let Some(mut slot) = env.get(&place.root) else {
        return Ok(());
    };
    for projection in &place.projections {
        let shared = match slot {
            Value::Array(a) => Arc::strong_count(a) > 1,
            Value::Dict(d) => Arc::strong_count(d) > 1,
            Value::ByteArray(b) => Arc::strong_count(b) > 1,
            Value::Object { fields, .. } => Arc::strong_count(fields) > 1,
            Value::ClassInstance(_) => return Ok(()),
            _ => false,
        };
        if shared {
            let ctx = ErrorContext::new().with_code(codes::INVALID_ASSIGNMENT).with_help(
                "assign through the place that owns the storage instead (pure-Simple and the seed JIT \
                 write through; this interpreter's containers are copy-on-write values); see \
                 doc/08_tracking/bug/seed_interp_call_root_shared_write_dropped_2026-11-07.md",
            );
            return Err(CompileError::semantic_with_context(
                "invalid assignment: call-result place root reaches storage that is still shared; \
                 the seed interpreter cannot write through it and refuses rather than drop the write",
                ctx,
            ));
        }
        match step_ref(slot, projection) {
            Some(next) => slot = next,
            None => return Ok(()),
        }
    }
    Ok(())
}

/// A call-result root bound by [`bind_call_root`]: the hidden binding name and
/// whatever that name held before, restored by [`unbind_call_root`].
pub(crate) struct CallRootBinding {
    name: String,
    saved: Option<Value>,
}

/// For a projection place rooted at a call result (`get()[i()]`,
/// `make().items[k]`), evaluate the call once, bind the value to a hidden
/// local and return the place rewritten onto that local. `resolve_place` then
/// evaluates the index subexpressions after the root, which is the owner
/// contract of 2026-11-06: RHS first, then the root, then indices outer to
/// inner, each once. Returns `None` when the root is not a call; such places
/// keep their existing handling. Writers call [`refuse_shared_call_root`] on
/// the resolved place before writing.
/// Bug: doc/08_tracking/bug/seed_interp_call_root_place_order_2026-11-06.md
pub(crate) fn bind_call_root(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<(Expr, CallRootBinding)>, CompileError> {
    fn root_of(expr: &Expr) -> &Expr {
        match expr {
            Expr::FieldAccess { receiver, .. } | Expr::Index { receiver, .. } => root_of(receiver),
            Expr::ForceUnwrap(inner) => root_of(inner),
            other => other,
        }
    }
    fn replace_root(expr: &Expr, name: &str) -> Expr {
        match expr {
            Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
                receiver: Box::new(replace_root(receiver, name)),
                field: field.clone(),
            },
            Expr::Index { receiver, index } => Expr::Index {
                receiver: Box::new(replace_root(receiver, name)),
                index: index.clone(),
            },
            Expr::ForceUnwrap(inner) => Expr::ForceUnwrap(Box::new(replace_root(inner, name))),
            _ => Expr::Identifier(name.to_string()),
        }
    }
    if !matches!(expr, Expr::FieldAccess { .. } | Expr::Index { .. }) {
        return Ok(None);
    }
    let root = root_of(expr);
    if !matches!(root, Expr::Call { .. } | Expr::MethodCall { .. }) {
        return Ok(None);
    }
    let root_value = evaluate_expr(root, env, functions, classes, enums, impl_methods)?;
    // NUL-prefixed: no Simple program can spell (and so clobber) this binding.
    let name = CALL_ROOT_BINDING.to_string();
    let saved = env.get(&name).cloned();
    env.insert(name.clone(), root_value);
    let rewritten = replace_root(expr, &name);
    Ok(Some((rewritten, CallRootBinding { name, saved })))
}

/// Restore the hidden binding that [`bind_call_root`] replaced.
pub(crate) fn unbind_call_root(env: &mut Env, binding: CallRootBinding) {
    match binding.saved {
        Some(value) => {
            env.insert(binding.name, value);
        }
        None => {
            env.remove(&binding.name);
        }
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

/// Borrow exactly the value that the expression-level force unwrap reads.
/// Canonical None/Err and nil have no writable payload; user enums and direct
/// nullable values retain their identity. Never clone a payload for a write.
fn unwrap_place_ref(slot: &Value) -> Option<&Value> {
    match slot {
        Value::Nil => None,
        Value::Enum { enum_name, variant, payload }
            if SpecialEnumType::from_name(enum_name).is_some() =>
        {
            match SpecialEnumKind::from_names(enum_name, variant) {
                Some(SpecialEnumKind::OptionSome | SpecialEnumKind::ResultOk) => payload.as_deref(),
                _ => None,
            }
        }
        other => Some(other),
    }
}

fn unwrap_place_mut(slot: &mut Value) -> Option<&mut Value> {
    match slot {
        Value::Nil => None,
        Value::Enum { enum_name, variant, payload }
            if SpecialEnumType::from_name(enum_name).is_some() =>
        {
            match SpecialEnumKind::from_names(enum_name, variant) {
                Some(SpecialEnumKind::OptionSome | SpecialEnumKind::ResultOk) => payload.as_deref_mut(),
                _ => None,
            }
        }
        other => Some(other),
    }
}

/// Take one projection step, yielding a mutable reference to the projected
/// storage. `Arc::make_mut` keeps copy-on-write semantics: unique containers
/// mutate in place, shared ones deep-copy first.
fn step_mut<'a>(slot: &'a mut Value, projection: &Projection) -> Option<&'a mut Value> {
    if matches!(projection, Projection::Unwrap) {
        return unwrap_place_mut(slot);
    }
    match (slot, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => Arc::make_mut(fields).get_mut(name),
        (Value::Dict(entries), Projection::Field(name)) => crate::interpreter::module_dict_make_mut(entries).get_mut(name),
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
            // Non-text keys are stored wrapped by `Value::wrap_dict_entry`; the
            // place is the value slot inside that wrapper.
            let key_string = key.to_key_string();
            crate::interpreter::module_dict_make_mut(entries)
                .get_mut(&key_string)
                .map(Value::dict_entry_value_mut)
        }
        (other, _) => {
            classinstance_tripwire("place::step_mut", other);
            None
        }
    }
}

/// Diagnostic tripwire (class-value-identity bug, step 1 of its plan): report
/// to stderr, once per site, when a `Value::ClassInstance` reaches a
/// `Value::Object`-only wildcard arm. Enabled by
/// `SIMPLE_INTERP_CLASSINSTANCE_TRIPWIRE=1`, read once; a single bool load when off.
pub(crate) fn classinstance_tripwire(site: &'static str, value: &Value) {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    static SEEN: Mutex<Vec<&'static str>> = Mutex::new(Vec::new());
    let enabled = *ENABLED.get_or_init(|| std::env::var("SIMPLE_INTERP_CLASSINSTANCE_TRIPWIRE").as_deref() == Ok("1"));
    tripwire_report(enabled, &SEEN, site, value);
}

/// Returns true when a report was emitted (enabled, a ClassInstance, first hit for `site`).
fn tripwire_report(enabled: bool, seen: &Mutex<Vec<&'static str>>, site: &'static str, value: &Value) -> bool {
    if !enabled {
        return false;
    }
    let Value::ClassInstance(instance) = value else {
        return false;
    };
    let mut seen = seen.lock().unwrap();
    if seen.contains(&site) {
        return false;
    }
    seen.push(site);
    eprintln!("[classinstance-tripwire] ClassInstance `{}` reached Value::Object wildcard at {}", instance.class(), site);
    true
}

/// Walk every projection, returning a mutable reference to the final storage.
fn project_mut<'a>(root: &'a mut Value, projections: &[Projection]) -> Option<&'a mut Value> {
    let mut slot = root;
    for projection in projections {
        slot = step_mut(slot, projection)?;
    }
    Some(slot)
}

/// Merge container-handle mutations from a callee parameter back into the
/// storage `projections` designate, starting from a clone of the place's
/// ROOT value (the caller's binding). Only the leaf merge runs the
/// shared-container carry (see `merge_shared_collection_fields`); scalar
/// fields keep value semantics. Returns true when the root changed.
pub(crate) fn merge_place_containers(root: &mut Value, projections: &[Projection], binding: &Value) -> bool {
    let Some(leaf) = project_mut(root, projections) else {
        return false;
    };
    crate::interpreter::interpreter_call::merge_shared_collection_fields(leaf, binding)
}

/// Write `value` at the end of `projections`, starting from `slot`.
///
/// The COW hops (`Object`, `Array`, `Dict`, tuples) are `step_mut` +
/// `store_last`, unchanged. A `Value::ClassInstance` hop is the reference
/// carrier (`SIMPLE_INTERP_CLASS_REF=1`): its field lives behind an `RwLock`,
/// so no `&mut Value` can be handed down the path. The field value is moved out
/// (`replace_field`), the nested write runs with NO lock held, and the value
/// is put back. Holding the write lock across the recursion instead would
/// deadlock on any path that revisits the same instance (`a.self_ref.v = 1`,
/// `a.items[0].v = 1` with `items[0] == a`), which cyclic class graphs do.
/// A nested `ClassInstance` is shared through its Arc, so the write lands in
/// the shared cell and the put-back stores the same Arc; a nested COW
/// container is uniquely held while moved out, so `Arc::make_mut` mutates it
/// in place rather than deep-copying.
fn write_through(slot: &mut Value, projections: &[Projection], value: Value) -> bool {
    let Some((head, rest)) = projections.split_first() else {
        return false;
    };
    if rest.is_empty() {
        return store_last(slot, head, value);
    }
    if let (Value::ClassInstance(instance), Projection::Field(name)) = (&*slot, head) {
        let Some(mut inner) = instance.replace_field(name, Value::Nil) else {
            return false;
        };
        let written = write_through(&mut inner, rest, value);
        instance.replace_field(name, inner);
        return written;
    }
    match step_mut(slot, head) {
        Some(next) => write_through(next, rest, value),
        None => false,
    }
}

/// Store `value` at the final projection of `container`.
///
/// The last step is an *insert*, not a navigation: assigning a field that does
/// not exist yet creates it, matching what the existing one- and two-level
/// field-assignment paths do with `HashMap::insert`.
fn store_last(container: &mut Value, projection: &Projection, value: Value) -> bool {
    if matches!(projection, Projection::Unwrap) {
        return match unwrap_place_mut(container) {
            Some(payload) => {
                *payload = value;
                true
            }
            None => false,
        };
    }
    match (container, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => {
            Arc::make_mut(fields).insert(name.clone(), value);
            true
        }
        (Value::Dict(entries), Projection::Field(name)) => {
            crate::interpreter::module_dict_make_mut(entries).insert(name.clone(), value);
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
            crate::interpreter::module_dict_make_mut(entries)
                .insert(key.to_key_string(), Value::wrap_dict_entry(key, value));
            true
        }
        // Reference carrier: the write lands in the shared cell, so every
        // holder of the instance (`val e = d["k"]`, the dict entry, a list
        // element) observes it — the JIT's class semantics.
        (Value::ClassInstance(instance), Projection::Field(name)) => {
            instance.set_field(name.clone(), value);
            true
        }
        (other, _) => {
            classinstance_tripwire("place::store_last", other);
            false
        }
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
    if place.projections.is_empty() {
        // No projections: a bare variable write.
        env.insert(place.root.clone(), value);
        sync_module_global(env, &place.root);
        return true;
    }
    let Some(root_slot) = env.get_mut(&place.root) else {
        return false;
    };
    if !write_through(root_slot, &place.projections, value) {
        return false;
    }
    sync_module_global(env, &place.root);
    true
}

/// Mirror a mutated root back into MODULE_GLOBALS when it is a module-level
/// binding, matching what the identifier and two-level paths already do.
pub(crate) fn sync_module_global(env: &mut Env, root: &str) {
    // A global with owner provenance publishes to its defining owner's store,
    // which is what reads resolve through. The flat map's entry under this
    // bare name may be an unrelated module's, so an import never writes it.
    if !env.is_local(root) {
        if let Some((owner, source_name)) = env.global_binding(root) {
            let foreign = env.scope().map_or(true, |scope| *scope.owner() != owner);
            if let Some(value) = env.get(root).cloned() {
                let scoped = env.scope().is_some();
                if scoped {
                    env.release_scope();
                }
                crate::interpreter::set_owned_global(&owner, &source_name, value, false);
                if scoped {
                    env.refresh_scope(crate::interpreter::owned_globals_snapshot());
                }
            }
            if foreign {
                return;
            }
        }
    }
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
    if place.projections.is_empty() {
        return None;
    }
    write_through(&mut root, &place.projections, value).then_some(root)
}

/// Borrow the storage the place designates, **without** touching ownership.
///
/// Read-only on purpose: a caller that only wants to know what KIND of value
/// sits at the leaf (an array? a dict? an object with this method?) must not
/// pay a copy-on-write isolation just to look. Pairs with `place_slot_mut`,
/// which is the same walk with `Arc::make_mut` once the caller has committed.
pub(crate) fn place_slot_ref<'a>(env: &'a Env, place: &Place) -> Option<&'a Value> {
    let mut slot = env.get(&place.root)?;
    for projection in &place.projections {
        slot = step_ref(slot, projection)?;
    }
    Some(slot)
}

/// Mutably borrow the storage the place designates, isolating exactly the
/// containers on the path (`Arc::make_mut` per hop) and nothing else.
///
/// This is the O(depth) counterpart of `updated_root`, which clones the root
/// value FIRST and therefore aliases every Arc along the path — making each hop's
/// `Arc::make_mut` a deep copy. Callers that mutate the leaf in place (a
/// mutating method on `self.inner.xs`, `rows[i]`, `self.d`) must use this.
pub(crate) fn place_slot_mut<'a>(env: &'a mut Env, place: &Place) -> Option<&'a mut Value> {
    let root_slot = env.get_mut(&place.root)?;
    project_mut(root_slot, &place.projections)
}

/// Before writing through a place that user code (an RHS or an index) has
/// just run against, reload a module-global root from MODULE_GLOBALS, which is
/// authoritative for non-local bindings, so a write cannot publish a stale
/// env snapshot over the user code's update.
pub(crate) fn refresh_module_global_root(env: &mut Env, root: &str) {
    if env.is_local(root) {
        return;
    }
    // A global with owner provenance reads through its owner's store, the
    // same store `sync_module_global` publishes to.
    if let Some((owner, source_name)) = env.global_binding(root) {
        if let Some(current) = super::interpreter_state::owned_global(&owner, &source_name) {
            env.insert(root.to_string(), current);
        }
        return;
    }
    if let Some(current) = MODULE_GLOBALS.with(|cell| cell.borrow().get(root).cloned()) {
        env.insert(root.to_string(), current);
    }
}

/// Owned read of the value the place designates. Unlike `place_slot_ref` it
/// also reads packed array elements and `ClassInstance` fields (neither has a
/// `&Value` to lend). Used by `place op= rhs`, which needs the old value once.
pub(crate) fn place_read(env: &Env, place: &Place) -> Option<Value> {
    let mut current = env.get(&place.root)?.clone();
    for projection in &place.projections {
        current = match (&current, projection) {
            (Value::ClassInstance(instance), Projection::Field(name)) => instance.field(name)?,
            (Value::Array(items), Projection::Index(index)) => items.get_value(normalize_index(items.len(), index)?)?,
            (Value::ByteArray(bytes), Projection::Index(index)) => {
                let idx = normalize_index(bytes.len(), index)?;
                Value::UInt { value: u64::from(bytes[idx]), width: 8 }
            }
            _ => step_ref(&current, projection)?.clone(),
        };
    }
    Some(current)
}

/// Read-only counterpart of `step_mut`.
fn step_ref<'a>(slot: &'a Value, projection: &Projection) -> Option<&'a Value> {
    if matches!(projection, Projection::Unwrap) {
        return unwrap_place_ref(slot);
    }
    match (slot, projection) {
        (Value::Object { fields, .. }, Projection::Field(name)) => fields.get(name),
        (Value::Dict(entries), Projection::Field(name)) => entries.get(name),
        // A packed array's elements are scalars (`Int` / `u32`) with no `Value`
        // to borrow; answering "no slot" instead of building the boxed view is
        // equivalent for every caller: a scalar leaf is never a mutation target
        // (`try_place_mutation_in_place` declines it either way) and no
        // projection continues past a scalar. Leaf EXISTENCE is answered by
        // `step_exists`, which does not need a reference.
        (Value::Array(items), Projection::Index(_)) if items.is_packed() => None,
        (Value::Array(items), Projection::Index(index)) => items.get(normalize_index(items.len(), index)?),
        (Value::FixedSizeArray { data, .. }, Projection::Index(index)) => data.get(normalize_index(data.len(), index)?),
        (Value::Tuple(items), Projection::Index(index)) => items.get(normalize_index(items.len(), index)?),
        (Value::Dict(entries), Projection::Index(key)) => {
            entries.get(&key.to_key_string()).map(Value::dict_entry_value_ref)
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
    let Some(slot) = env.get(&place.root) else {
        return false;
    };
    // The final projection is an insert target, so it need not exist yet; every
    // intermediate hop must.
    if place.projections.is_empty() {
        return true;
    }
    projections_live(slot, &place.projections)
}

/// Walk `projections` from `slot`. A `Value::ClassInstance` hop keeps its
/// fields behind a lock, so no reference can be borrowed through it; the field
/// is read (an Arc-handle clone) and the walk continues on the owned value.
/// Without this, `self.store.items.push(x)` (a class field holding a class)
/// was never a live place and the mutation hit a throwaway copy.
fn projections_live(slot: &Value, projections: &[Projection]) -> bool {
    let Some((head, rest)) = projections.split_first() else {
        return true;
    };
    if rest.is_empty() {
        // The leaf must exist for a receiver read to make sense.
        return step_exists(slot, head);
    }
    if let (Value::ClassInstance(instance), Projection::Field(name)) = (slot, head) {
        return match instance.field(name) {
            Some(next) => projections_live(&next, rest),
            None => false,
        };
    }
    match step_ref(slot, head) {
        Some(next) => projections_live(next, rest),
        None => false,
    }
}

/// Whether `projection` names an existing slot of `slot` -- `step_ref(..).is_some()`
/// without needing a reference (a packed array element has none).
fn step_exists(slot: &Value, projection: &Projection) -> bool {
    match (slot, projection) {
        (Value::Array(items), Projection::Index(index)) if items.is_packed() => {
            normalize_index(items.len(), index).is_some()
        }
        // The reference carrier's fields sit behind a lock, so there is no
        // reference to hand out; existence is answered by a read.
        (Value::ClassInstance(instance), Projection::Field(name)) => instance.field(name).is_some(),
        _ => step_ref(slot, projection).is_some(),
    }
}

/// One step from a match subject (or an argument root) to the storage an arm
/// payload binding aliases inside it. `Payload` exists only for enum subjects
/// (`case Ram(d)` binds `d` to the variant payload).
#[derive(Debug, Clone)]
pub(crate) enum SubjectStep {
    /// Enum variant payload.
    Payload,
    /// Struct/class field by name.
    Field(String),
    /// Array/tuple element by literal index.
    Index(i64),
}

/// Merge container-handle mutations from an arm payload binding back into the
/// subject storage it aliases, following `steps` from `slot`. The leaf merge
/// is `merge_shared_collection_fields`: only shared containers (array/dict/
/// bytearray handles, including ones nested inside payload structs) are
/// carried back, so value semantics for scalar fields are preserved exactly.
/// Returns true when `slot` changed.
pub(crate) fn merge_subject_step(slot: &mut Value, steps: &[SubjectStep], binding: &Value) -> bool {
    let Some((head, rest)) = steps.split_first() else {
        return crate::interpreter::interpreter_call::merge_shared_collection_fields(slot, binding);
    };
    match (slot, head) {
        (Value::Enum { payload: Some(payload), .. }, SubjectStep::Payload) => {
            merge_subject_step(&mut **payload, rest, binding)
        }
        (Value::Object { fields, .. }, SubjectStep::Field(name)) => {
            if !fields.contains_key(name) {
                return false;
            }
            let field = Arc::make_mut(fields).get_mut(name).expect("field presence checked");
            merge_subject_step(field, rest, binding)
        }
        // Reference-semantics class on the path: merge into the shared cell.
        // The child is cloned out (not borrowed under the write lock) so a
        // self-referencing chain cannot deadlock; a class child is a handle
        // to its own cell and needs no store-back.
        (Value::ClassInstance(instance), SubjectStep::Field(name)) => {
            let Some(mut child) = instance.field(name) else {
                return false;
            };
            if !merge_subject_step(&mut child, rest, binding) {
                return false;
            }
            if !matches!(child, Value::ClassInstance(_)) {
                instance.set_field(name.clone(), child);
            }
            true
        }
        (Value::Array(items), SubjectStep::Index(index)) => {
            let Some(idx) = normalize_index(items.len(), &Value::Int(*index)) else {
                return false;
            };
            let elem = match Arc::get_mut(items).and_then(|data| data.get_mut(idx)) {
                Some(elem) => elem,
                None => Arc::make_mut(items).get_mut(idx).expect("index in bounds"),
            };
            merge_subject_step(elem, rest, binding)
        }
        (Value::Tuple(items), SubjectStep::Index(index)) => {
            let Ok(idx) = usize::try_from(*index) else {
                return false;
            };
            let Some(elem) = items.get_mut(idx) else {
                return false;
            };
            merge_subject_step(elem, rest, binding)
        }
        _ => false,
    }
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

    fn p1_enum_opt_wrapped(owner: &str, variant: &str, payload: Option<Value>) -> Value {
        Value::Enum {
            enum_name: owner.into(),
            variant: variant.into(),
            payload: payload.map(Box::new),
        }
    }

    #[test]
    fn forceunwrap_place_keeps_option_and_result_wrappers_and_cow_aliases() {
        for (owner, variant) in [("Option", "Some"), ("Result", "Ok")] {
            let wrapped = p1_enum_opt_wrapped(owner, variant,
                Some(object("Cell", vec![("n", Value::Int(5))])));
            let mut env = Env::new();
            env.insert("item".into(), wrapped.clone());
            env.insert("alias".into(), wrapped);
            let place = Place { root: "item".into(),
                projections: vec![Projection::Unwrap, Projection::Field("n".into())] };
            assert!(place_is_live(&env, &place));
            assert_eq!(place_read(&env, &place), Some(Value::Int(5)));
            assert!(write_place(&mut env, &place, Value::Int(7)));
            assert_eq!(place_read(&env, &place), Some(Value::Int(7)));
            let alias = Place { root: "alias".into(), projections: place.projections.clone() };
            assert_eq!(place_read(&env, &alias), Some(Value::Int(5)));
            assert!(matches!(env.get("item"), Some(Value::Enum { enum_name, variant: actual, .. })
                if enum_name == owner && actual == variant));
        }
    }

    #[test]
    fn forceunwrap_place_rejects_absent_and_malformed_special_values_without_writes() {
        for original in [Value::Nil,
            p1_enum_opt_wrapped("Option", "None", None),
            p1_enum_opt_wrapped("Option", "Some", None),
            p1_enum_opt_wrapped("Result", "Err", Some(Value::Int(5))),
            p1_enum_opt_wrapped("Result", "Ok", None),
            p1_enum_opt_wrapped("Option", "Bad", Some(Value::Int(5))),
        ] {
            let mut env = Env::new();
            env.insert("item".into(), original.clone());
            let place = Place { root: "item".into(), projections: vec![Projection::Unwrap] };
            assert!(!place_is_live(&env, &place));
            assert_eq!(place_read(&env, &place), None);
            assert!(!write_place(&mut env, &place, Value::Int(7)));
            let field = Place { root: "item".into(),
                projections: vec![Projection::Unwrap, Projection::Field("n".into())] };
            assert!(!write_place(&mut env, &field, Value::Int(7)));
            assert_eq!(env.get("item"), Some(&original));
        }
    }

    #[test]
    fn forceunwrap_place_is_identity_for_direct_values_and_user_enums() {
        for original in [Value::Int(5),
            p1_enum_opt_wrapped("UserOption", "Some", Some(Value::Int(5))),
            object("Cell", vec![("n", Value::Int(5))]),
        ] {
            assert!(std::ptr::eq(unwrap_place_ref(&original).unwrap(), &original));
            let mut copy = original;
            *unwrap_place_mut(&mut copy).unwrap() = Value::Int(7);
            assert_eq!(copy, Value::Int(7));
        }
    }

    #[test]
    fn forceunwrap_place_nested_payload_replacement_preserves_outer_wrappers() {
        let mut env = Env::new();
        env.insert("item".into(), p1_enum_opt_wrapped("Option", "Some",
            Some(p1_enum_opt_wrapped("Result", "Ok", Some(Value::Int(5))))));
        let place = Place { root: "item".into(),
            projections: vec![Projection::Unwrap, Projection::Unwrap] };
        assert!(write_place(&mut env, &place, Value::Int(7)));
        assert_eq!(env.get("item"), Some(&p1_enum_opt_wrapped("Option", "Some",
            Some(p1_enum_opt_wrapped("Result", "Ok", Some(Value::Int(7)))))));
    }

    #[test]
    fn forceunwrap_place_preserves_shared_class_identity() {
        use crate::value::ClassInstance;
        let instance = Arc::new(ClassInstance::new("Cell".into(),
            [("n".into(), Value::Int(5))].into_iter().collect()));
        let mut env = Env::new();
        env.insert("item".into(), p1_enum_opt_wrapped("Option", "Some",
            Some(Value::ClassInstance(instance.clone()))));
        let place = Place { root: "item".into(),
            projections: vec![Projection::Unwrap, Projection::Field("n".into())] };
        assert!(write_place(&mut env, &place, Value::Int(7)));
        assert_eq!(instance.field("n"), Some(Value::Int(7)));
    }

    #[test]
    fn forceunwrap_place_resolver_keeps_unwrap_and_index_observation() {
        let mut env = Env::new();
        env.insert("item".into(), p1_enum_opt_wrapped("Option", "Some", Some(Value::Int(5))));
        let expr = Expr::ForceUnwrap(Box::new(Expr::Identifier("item".into())));
        let place = resolve_place(&expr, &mut env, &mut HashMap::new(), &mut HashMap::new(),
            &Default::default(), &Default::default()).unwrap().unwrap();
        assert!(matches!(place.projections.as_slice(), [Projection::Unwrap]));
        let indexed = Expr::ForceUnwrap(Box::new(Expr::Index {
            receiver: Box::new(Expr::Identifier("items".into())),
            index: Box::new(Expr::Identifier("index".into())),
        }));
        assert!(place_has_index(&indexed));
        assert!(!place_has_index(&expr));
        let missing = Expr::ForceUnwrap(Box::new(Expr::Identifier("missing".into())));
        assert!(resolve_place(&missing, &mut env, &mut HashMap::new(), &mut HashMap::new(),
            &Default::default(), &Default::default()).unwrap().is_none());
    }

    #[test]
    fn classinstance_tripwire_fires_once_per_site_only_when_enabled() {
        use crate::value::ClassInstance;
        let ci = Value::ClassInstance(Arc::new(ClassInstance::new("Inner".to_string(), HashMap::new())));
        let seen = Mutex::new(Vec::new());
        assert!(!tripwire_report(false, &seen, "t::site", &ci), "off: silent");
        assert!(!tripwire_report(true, &seen, "t::site", &Value::Int(1)), "non-ClassInstance: silent");
        assert!(tripwire_report(true, &seen, "t::site", &ci), "first hit reports");
        assert!(!tripwire_report(true, &seen, "t::site", &ci), "once per site");
        assert!(tripwire_report(true, &seen, "t::other", &ci), "new site reports");
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
        let holder = object("Holder", vec![("items", Value::array(vec![elem]))]);

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

    fn class_instance(class: &str, fields: Vec<(&str, Value)>) -> (Arc<crate::value::ClassInstance>, Value) {
        let inst = Arc::new(crate::value::ClassInstance::new(
            class.to_string(),
            fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect(),
        ));
        (Arc::clone(&inst), Value::ClassInstance(inst))
    }

    /// `d["k"].v = 2` on the reference carrier: the write lands in the SHARED
    /// cell, so a binding taken earlier (`val e = d["k"]`) sees it too.
    /// Bug: interp_dict_class_value_index_mutation_loss_2026-11-03.
    #[test]
    fn write_through_dict_value_class_instance_is_shared() {
        let (inst, value) = class_instance("Inner", vec![("v", Value::Int(0))]);
        let dict: crate::value::DictMap = [("k".to_string(), value)].into_iter().collect();
        let mut env = Env::new();
        env.insert("d".into(), Value::Dict(Arc::new(dict)));

        let place = Place {
            root: "d".into(),
            projections: vec![Projection::Index(Value::text("k")), Projection::Field("v".into())],
        };
        assert!(place_is_live(&env, &place), "an existing class field is a live leaf");
        assert!(write_place(&mut env, &place, Value::Int(2)));
        assert_eq!(inst.field("v"), Some(Value::Int(2)), "the earlier holder observes the write");
        match env.get("d").unwrap() {
            Value::Dict(entries) => match entries.get("k").unwrap() {
                Value::ClassInstance(stored) => assert!(Arc::ptr_eq(stored, &inst), "entry identity kept"),
                other => panic!("not a class instance: {:?}", other),
            },
            other => panic!("not a dict: {:?}", other),
        }
    }

    /// A ClassInstance as an INTERMEDIATE hop (`o.d["k"].v = 2`, `o.items[0].n = 9`):
    /// the COW container inside it is written in place, not deep-copied.
    #[test]
    fn write_through_class_instance_hop_into_cow_container() {
        let elem = object("Elem", vec![("n", Value::Int(1))]);
        let (inst, holder) = class_instance("Holder", vec![("items", Value::array(vec![elem]))]);
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
        match inst.field("items") {
            Some(Value::Array(values)) => match &values[0] {
                Value::Object { fields, .. } => assert_eq!(fields.get("n").unwrap().clone(), Value::Int(99)),
                other => panic!("not an object: {:?}", other),
            },
            other => panic!("not an array: {:?}", other),
        }
    }

    /// A path that revisits the same instance (`a.me.v = 7` with `a.me == a`)
    /// must complete instead of deadlocking on the instance's own lock.
    #[test]
    fn write_through_cyclic_class_instance_does_not_deadlock() {
        let (inst, value) = class_instance("Node", vec![("v", Value::Int(0)), ("me", Value::Nil)]);
        inst.set_field("me".into(), Value::ClassInstance(Arc::clone(&inst)));
        let mut env = Env::new();
        env.insert("a".into(), value);

        let place = Place {
            root: "a".into(),
            projections: vec![Projection::Field("me".into()), Projection::Field("v".into())],
        };
        // Holding `a`'s write lock across the nested hop would block here forever.
        assert!(write_place(&mut env, &place, Value::Int(7)));
        assert_eq!(inst.field("v"), Some(Value::Int(7)));
        match inst.field("me") {
            Some(Value::ClassInstance(me)) => assert!(Arc::ptr_eq(&me, &inst), "self link restored"),
            other => panic!("self link lost: {:?}", other),
        }
    }

    #[test]
    fn missing_field_reports_not_live_instead_of_erroring() {
        let root = object("Root", vec![("mid", Value::Int(0))]);
        let mut env = Env::new();
        env.insert("root".into(), root);

        let place = Place {
            root: "root".into(),
            projections: vec![Projection::Field("mid".into()), Projection::Field("inner".into())],
        };
        assert!(!place_is_live(&env, &place));
        assert!(!write_place(&mut env, &place, Value::Int(1)));
    }

    #[test]
    fn out_of_bounds_index_is_not_a_live_place() {
        let holder = object("Holder", vec![("items", Value::array(vec![Value::Int(1)]))]);
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
