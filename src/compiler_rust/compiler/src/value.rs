//! Value types for the interpreter.
//!
//! This module contains the runtime value representation and
//! pointer wrapper types for manual memory management.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex, OnceLock, RwLock};

use simple_common::actor::ActorHandle;
use simple_common::manual_mem::{
    Handle as ManualHandle, HandlePool as ManualHandlePool, ManualGc, Shared as ManualShared, Unique as ManualUnique,
    WeakPtr as ManualWeak,
};
use simple_parser::ast::{Expr, FunctionDef, Node};

use crate::error::{codes, CompileError, ErrorContext};

pub type SharedText = Arc<String>;

/// Frequently-used enum type and variant names as constants.
/// Eliminates repeated string allocation at hot paths and establishes
/// a single source of truth for these names.
pub mod enum_names {
    pub const OPTION: &str = "Option";
    pub const SOME: &str = "Some";
    pub const NONE: &str = "None";
    pub const RESULT: &str = "Result";
    pub const OK: &str = "Ok";
    pub const ERR: &str = "Err";
}

// Async value types (Future, Generator, Channel, ThreadPool)
// These are split into a separate file for maintainability
include!("value_async.rs");

// Mock and Spy types for testing
include!("value_mock.rs");

//==============================================================================
// Magic Names (for formal verification)
//==============================================================================
// These constants define the special names used by the interpreter.
// Making them constants ensures consistency and enables Lean verification.
//
// Lean equivalent:
//   def BUILTIN_RANGE : String := "__range__"
//   def BUILTIN_ARRAY : String := "__array__"
//   def METHOD_NEW : String := "new"
//   def METHOD_SELF : String := "self"
//   def METHOD_MISSING : String := "method_missing"
//   def FUNC_MAIN : String := "main"
//   def ATTR_STRONG : String := "strong"

/// Magic class name for range objects created by range() or `..` syntax
pub const BUILTIN_RANGE: &str = "__range__";

/// Magic class name for array-like objects
pub const BUILTIN_ARRAY: &str = "__array__";

//==============================================================================
// Special Method Names (for formal verification)
//==============================================================================

/// Constructor method name
pub const METHOD_NEW: &str = "new";

/// Self parameter name
pub const METHOD_SELF: &str = "self";

/// Method missing hook name (Ruby-style metaprogramming)
pub const METHOD_MISSING: &str = "method_missing";

/// Entry point function name
pub const FUNC_MAIN: &str = "main";

//==============================================================================
// Special Attribute Names (for formal verification)
//==============================================================================

/// Strong enum attribute (enforces exhaustive matching)
pub const ATTR_STRONG: &str = "strong";

//==============================================================================
// Built-in Type/Function Names (for formal verification)
//==============================================================================

/// Channel constructor name
pub const BUILTIN_CHANNEL: &str = "Channel";

/// Spawn function name for actor creation
pub const BUILTIN_SPAWN: &str = "spawn";

/// Join function name for actor synchronization
pub const BUILTIN_JOIN: &str = "join";

/// Reply function name for actor message response
pub const BUILTIN_REPLY: &str = "reply";

/// User-facing Range class name (alias for BUILTIN_RANGE)
pub const CLASS_RANGE: &str = "Range";

/// User-facing Array class name (alias for BUILTIN_ARRAY)
pub const CLASS_ARRAY: &str = "Array";

//==============================================================================
// Builtin Operation Categories (for formal verification)
//==============================================================================
// These arrays define categories of builtin operations for effect analysis.
// Making them constants enables Lean verification of effect properties.

/// Blocking operations - cannot be used in async contexts
pub const BLOCKING_BUILTINS: &[&str] = &[
    "await",
    "join",
    "recv",
    "sleep",
    "input",
    "read_file",
    "write_file",
    // Native filesystem operations
    "native_fs_read",
    "native_fs_write",
    "native_fs_append",
    "native_fs_create_dir",
    "native_fs_remove_file",
    "native_fs_remove_dir",
    "native_fs_rename",
    "native_fs_copy",
    "native_fs_metadata",
    "native_fs_read_dir",
    "native_fs_open",
    "native_file_read",
    "native_file_write",
    "native_file_flush",
    "native_file_seek",
    "native_file_sync",
    "native_file_close",
    // Native terminal operations
    "native_term_read",
    "native_term_write",
    "native_term_read_timeout",
    "native_term_flush",
    "native_term_poll",
];

/// Actor operations - require actor runtime
pub const ACTOR_BUILTINS: &[&str] = &["spawn", "send", "recv", "reply", "join"];

/// Generator operations - require generator runtime
pub const GENERATOR_BUILTINS: &[&str] = &["generator", "next", "collect"];

/// Built-in class types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive BuiltinClass
///   | range   -- Range objects (start..end)
///   | array   -- Array-like objects
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinClass {
    /// Range type: represents a range of values
    Range,
    /// Array type: built-in array wrapper
    Array,
}

impl BuiltinClass {
    /// Try to parse a class name as a built-in class.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "__range__" | "Range" => Some(BuiltinClass::Range),
            "__array__" | "Array" => Some(BuiltinClass::Array),
            _ => None,
        }
    }

    /// Get the internal string name of this built-in class.
    pub fn as_str(&self) -> &'static str {
        match self {
            BuiltinClass::Range => BUILTIN_RANGE,
            BuiltinClass::Array => BUILTIN_ARRAY,
        }
    }

    /// Check if the given class name matches this built-in class.
    pub fn matches(&self, name: &str) -> bool {
        match self {
            BuiltinClass::Range => name == BUILTIN_RANGE || name == CLASS_RANGE,
            BuiltinClass::Array => name == BUILTIN_ARRAY || name == CLASS_ARRAY,
        }
    }
}

/// Classification of a class type - either builtin or user-defined.
///
/// Lean equivalent:
/// ```lean
/// inductive ClassType
///   | builtin (b : BuiltinClass)
///   | user (name : String)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassType {
    /// A built-in class with special handling
    Builtin(BuiltinClass),
    /// A user-defined class
    User(String),
}

impl ClassType {
    /// Classify a class name as either builtin or user-defined.
    pub fn from_name(name: &str) -> Self {
        match BuiltinClass::from_name(name) {
            Some(builtin) => ClassType::Builtin(builtin),
            None => ClassType::User(name.to_string()),
        }
    }

    /// Check if this is a built-in class.
    pub fn is_builtin(&self) -> bool {
        matches!(self, ClassType::Builtin(_))
    }

    /// Check if this is the range type.
    pub fn is_range(&self) -> bool {
        matches!(self, ClassType::Builtin(BuiltinClass::Range))
    }
}

//==============================================================================
// Method Lookup (for formal verification)
//==============================================================================
// These types replace magic string "method_missing" with explicit enum variants.
// This makes method dispatch logic verifiable.
// Note: METHOD_MISSING constant is defined above with other special names.

/// Result of looking up a method on a type.
///
/// Lean equivalent:
/// ```lean
/// inductive MethodLookupResult
///   | found           -- Regular method found
///   | notFound        -- Method not found, no fallback
///   | missingHook     -- method_missing fallback available
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodLookupResult {
    /// Regular method was found
    Found,
    /// Method not found and no method_missing hook
    NotFound,
    /// Method not found but method_missing hook is available
    MissingHook,
}

impl MethodLookupResult {
    /// Check if a method was found (either direct or via method_missing).
    pub fn is_callable(&self) -> bool {
        matches!(self, MethodLookupResult::Found | MethodLookupResult::MissingHook)
    }

    /// Check if this is the method_missing fallback.
    pub fn is_missing_hook(&self) -> bool {
        matches!(self, MethodLookupResult::MissingHook)
    }
}

// ---------------------------------------------------------------------------
// Strict interpreter mode (plan M5, "Miri-lite"): SIMPLE_STRICT_MEM=1.
// Gated: OFF by default, off-path is a single cached-bool relaxed load — no
// per-check env read, no lock. Mirrors `heap.rs` `ATTR_ENABLED`/
// `mem_attr_enabled()` and `nodes.spl` `ast_gen_check_enabled`.
// ---------------------------------------------------------------------------

static STRICT_MEM_ENABLED: OnceLock<bool> = OnceLock::new();
static STRICT_MEM_FORCED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

#[inline]
pub fn strict_mem_enabled() -> bool {
    STRICT_MEM_FORCED.load(std::sync::atomic::Ordering::Relaxed)
        || *STRICT_MEM_ENABLED
            .get_or_init(|| std::env::var("SIMPLE_STRICT_MEM").map(|v| v == "1").unwrap_or(false))
}

/// Programmatic enable (CLI `--mem-infra=strict` path, and tests). Effective
/// even after the env-derived `OnceLock` has been primed false — a plain
/// `OnceLock::set` here would silently lose to any earlier check (the exact
/// ordering trap the strict-mode integration test hit).
pub fn strict_mem_enable() {
    STRICT_MEM_FORCED.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// Live per-owner module-global stores: owner -> (name -> value). The outer
/// and inner maps are both `Arc`-shared so a call frame can SNAPSHOT the whole
/// store in O(1) (`GlobalScope`), while a write copies only the map it
/// touches (`Arc::make_mut`) — never the thousands of bindings a module env
/// used to materialize per call.
/// doc/08_tracking/bug/seed_interpreter_env_rebuild_per_call_o_globals_2026-08-21.md
pub type OwnedGlobals = Arc<HashMap<Arc<str>, Arc<HashMap<String, Value>>>>;

thread_local! {
    /// Shared empty store for released scopes (`CowEnv::release_scope`).
    static EMPTY_GLOBALS: OwnedGlobals = Arc::new(HashMap::new());
}

/// Per-module import table: local alias -> (defining owner, defining name),
/// plus the reverse index (owner -> name -> aliases) so every alias of a
/// written global is found in O(1) instead of scanning the whole table.
#[derive(Debug, Default, Clone)]
pub struct ModuleBindings {
    forward: HashMap<String, (Arc<str>, String)>,
    reverse: HashMap<Arc<str>, HashMap<String, Vec<String>>>,
}

impl ModuleBindings {
    pub fn insert(&mut self, local_name: String, binding: (Arc<str>, String)) {
        if let Some(old) = self.forward.get(&local_name) {
            if *old == binding {
                return;
            }
            if let Some(aliases) = self.reverse.get_mut(&old.0).and_then(|by_name| by_name.get_mut(&old.1)) {
                aliases.retain(|alias| alias != &local_name);
            }
        }
        self.reverse
            .entry(Arc::clone(&binding.0))
            .or_default()
            .entry(binding.1.clone())
            .or_default()
            .push(local_name.clone());
        self.forward.insert(local_name, binding);
    }

    pub fn get(&self, local_name: &str) -> Option<&(Arc<str>, String)> {
        self.forward.get(local_name)
    }

    /// Local aliases bound to (`owner`, `name`).
    pub fn aliases_of(&self, owner: &str, name: &str) -> &[String] {
        self.reverse
            .get(owner)
            .and_then(|by_name| by_name.get(name))
            .map(|aliases| aliases.as_slice())
            .unwrap_or(&[])
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &(Arc<str>, String))> {
        self.forward.iter()
    }

    pub fn len(&self) -> usize {
        self.forward.len()
    }

    pub fn is_empty(&self) -> bool {
        self.forward.is_empty()
    }
}

/// The module-level scope a call frame resolves globals through, by parent
/// pointer rather than by copy. Lookup order for a name not in the frame's
/// overlay: the owner's live globals, then its imports (resolved through the
/// defining owner's live globals), then the static module env (functions,
/// classes, constants). All four handles are `Arc`s: attaching a scope to a
/// frame is four refcount increments, independent of how many globals exist.
#[derive(Debug, Clone)]
pub struct GlobalScope {
    owner: Arc<str>,
    module_env: Option<Arc<HashMap<String, Value>>>,
    bindings: Option<Arc<ModuleBindings>>,
    globals: OwnedGlobals,
}

impl GlobalScope {
    pub fn new(
        owner: Arc<str>,
        module_env: Option<Arc<HashMap<String, Value>>>,
        bindings: Option<Arc<ModuleBindings>>,
        globals: OwnedGlobals,
    ) -> Self {
        GlobalScope {
            owner,
            module_env,
            bindings,
            globals,
        }
    }

    pub fn owner(&self) -> &Arc<str> {
        &self.owner
    }

    fn owner_globals(&self) -> Option<&Arc<HashMap<String, Value>>> {
        self.globals.get(&self.owner)
    }

    /// True while `release_scope` has pointed this scope at the shared empty
    /// store (the frame is not executing, or is about to write the store).
    fn is_released(&self) -> bool {
        EMPTY_GLOBALS.with(|empty| Arc::ptr_eq(&self.globals, empty))
    }

    /// Is `name` one of the owner's own module globals? Answered from the
    /// snapshot while one is held; from the live store while released. The
    /// released case is what `publish_and_repoint` and the callee-side sync
    /// run in, and answering "no" there silently dropped every publish of a
    /// frame's writes to its own module globals (stage-1 then read a
    /// one-append-stale arena: `index is 742 but length is 742`).
    fn owner_has(&self, name: &str) -> bool {
        if self.is_released() {
            return crate::interpreter::owned_global_present(&self.owner, name);
        }
        self.owner_globals().is_some_and(|globals| globals.contains_key(name))
    }

    /// Live value: owner globals first, then imported globals.
    fn get_live(&self, name: &str) -> Option<&Value> {
        if let Some(value) = self.owner_globals().and_then(|globals| globals.get(name)) {
            return Some(value);
        }
        let (owner, source) = self.bindings.as_ref()?.get(name)?;
        self.globals.get(owner)?.get(source.as_str())
    }

    fn get_static(&self, name: &str) -> Option<&Value> {
        self.module_env.as_ref()?.get(name)
    }

    fn contains_live(&self, name: &str) -> bool {
        self.get_live(name).is_some()
    }

    fn contains_static(&self, name: &str) -> bool {
        self.module_env.as_ref().is_some_and(|env| env.contains_key(name))
    }

    /// (defining owner, defining name) of a global visible as `name`.
    fn binding(&self, name: &str) -> Option<(Arc<str>, String)> {
        if self.owner_has(name) {
            return Some((Arc::clone(&self.owner), name.to_owned()));
        }
        self.bindings.as_ref()?.get(name).cloned()
    }

    /// Every local name through which (`owner`, `source`) is visible.
    fn aliases_of(&self, owner: &Arc<str>, source: &str, out: &mut Vec<String>) {
        if *owner == self.owner && self.owner_has(source) {
            out.push(source.to_owned());
        }
        if let Some(bindings) = &self.bindings {
            out.extend(bindings.aliases_of(owner, source).iter().cloned());
        }
    }

    fn for_each_binding<'a>(&'a self, mut f: impl FnMut(&'a String, (Arc<str>, String))) {
        if let Some(globals) = self.owner_globals() {
            for name in globals.keys() {
                f(name, (Arc::clone(&self.owner), name.clone()));
            }
        }
        if let Some(bindings) = &self.bindings {
            for (local_name, binding) in bindings.iter() {
                f(local_name, binding.clone());
            }
        }
    }

    /// Live-layer entries in precedence order (owner globals, then imports).
    fn for_each_live<'a>(&'a self, mut f: impl FnMut(&'a String, &'a Value)) {
        if let Some(globals) = self.owner_globals() {
            for (name, value) in globals.iter() {
                f(name, value);
            }
        }
        if let Some(bindings) = &self.bindings {
            for (local_name, (owner, source)) in bindings.iter() {
                if let Some(value) = self.globals.get(owner).and_then(|globals| globals.get(source.as_str())) {
                    f(local_name, value);
                }
            }
        }
    }
}

/// Copy-on-write environment: reads check the frame's overlay first, then the
/// module scope (live globals by parent pointer), then the immutable base.
/// Clone is O(overlay_size): base and scope are `Arc`s.
///
/// This replaces the old `type Env = HashMap<String, Value>` with a struct
/// that avoids deep-cloning the entire captured environment on every
/// function/lambda call.
#[derive(Debug)]
pub struct CowEnv {
    /// Shared immutable base environment (cheap to clone via Arc)
    base: Option<Arc<HashMap<String, Value>>>,
    /// Module scope resolved by parent pointer: never copied into the frame.
    scope: Option<GlobalScope>,
    /// Local modifications/additions (typically small — function args, locals)
    overlay: HashMap<String, Value>,
    /// Keys removed from base/scope (tombstones)
    tombstones: HashSet<String>,
    /// Names declared by the current lexical function frame.
    local_bindings: HashSet<String>,
    /// Names shadowed by currently executing nested blocks.
    block_local_bindings: HashMap<String, usize>,
    /// Owner-global values copied from a callee for reads, not caller writes.
    refreshed_globals: HashSet<String>,
    /// Owner-qualified updates crossing frames from another module.
    forwarded_globals: HashMap<(Arc<str>, String), Value>,
    /// Explicit local-name -> defining module/name bindings (selective lambda
    /// capture, tests). The module scope answers the same question lazily for
    /// every other name, so this stays small.
    global_bindings: Arc<HashMap<String, (Arc<str>, String)>>,
    /// Names written through this frame since the last `clear_dirty()`.
    /// Distinguishes actual frame writes from values merely present in a
    /// cloned environment, so block/closure write-back can be dirty-only.
    dirty_names: HashSet<String>,
    /// Strict-mode only (plan M5 §2): names bound by an initializer-less
    /// `let` that have not yet received a first assignment. Stays an
    /// unallocated empty `HashSet` when `SIMPLE_STRICT_MEM` is unset — no
    /// off-path cost beyond the field itself.
    uninit_names: HashSet<String>,
}

impl CowEnv {
    /// Create an empty environment.
    pub fn new() -> Self {
        CowEnv {
            base: None,
            scope: None,
            overlay: HashMap::new(),
            tombstones: HashSet::new(),
            local_bindings: HashSet::new(),
            block_local_bindings: HashMap::new(),
            refreshed_globals: HashSet::new(),
            forwarded_globals: HashMap::new(),
            global_bindings: Arc::new(HashMap::new()),
            dirty_names: HashSet::new(),
            uninit_names: HashSet::new(),
        }
    }

    /// Look up a key: overlay, then (skipping tombstones) the live module
    /// scope, the base, and finally the static module env.
    pub fn get(&self, key: &str) -> Option<&Value> {
        if let Some(v) = self.overlay.get(key) {
            return Some(v);
        }
        if self.tombstones.contains(key) {
            return None;
        }
        if let Some(scope) = &self.scope {
            if let Some(v) = scope.get_live(key) {
                return Some(v);
            }
        }
        if let Some(ref base) = self.base {
            if let Some(v) = base.get(key) {
                return Some(v);
            }
        }
        self.scope.as_ref().and_then(|scope| scope.get_static(key))
    }

    /// Insert a key-value pair. Returns the previous value if any.
    pub fn insert(&mut self, key: String, value: Value) -> Option<Value> {
        self.tombstones.remove(&key);
        self.refreshed_globals.remove(&key);
        self.dirty_names.insert(key.clone());
        // First assignment to a strict-mode uninit name clears its trap
        // (same removal point `tombstones` uses above).
        if !self.uninit_names.is_empty() {
            self.uninit_names.remove(&key);
        }
        self.overlay.insert(key, value)
    }

    /// Strict mode only (plan M5 §2): mark `name` as bound-but-uninitialized
    /// by an initializer-less `let`. No overlay entry is created, so a plain
    /// read still falls through today's lookup cascade unless this state is
    /// checked first (see `is_uninit`).
    pub fn mark_uninit(&mut self, name: impl Into<String>) {
        self.uninit_names.insert(name.into());
    }

    /// Strict mode only: true if `name` was `mark_uninit`-ed and has not yet
    /// received a first assignment via `insert`.
    pub fn is_uninit(&self, name: &str) -> bool {
        self.uninit_names.contains(name)
    }

    pub fn mark_local(&mut self, name: impl Into<String>) {
        let name = name.into();
        if self.global_bindings.contains_key(&name) {
            Arc::make_mut(&mut self.global_bindings).remove(&name);
        }
        self.local_bindings.insert(name);
    }

    pub fn enter_block_local(&mut self, name: impl Into<String>) {
        *self.block_local_bindings.entry(name.into()).or_default() += 1;
    }

    pub fn exit_block_local(&mut self, name: &str) {
        let Some(depth) = self.block_local_bindings.get_mut(name) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.block_local_bindings.remove(name);
        }
    }

    pub fn is_local(&self, name: &str) -> bool {
        self.local_bindings.contains(name) || self.block_local_bindings.contains_key(name)
    }

    /// Attach (or replace) the module scope this frame resolves globals through.
    pub fn set_scope(&mut self, scope: GlobalScope) {
        self.scope = Some(scope);
    }

    pub fn scope(&self) -> Option<&GlobalScope> {
        self.scope.as_ref()
    }

    /// Re-point the scope at the current live stores. O(1): the frame keeps
    /// no copy of any global, so "refreshing" is swapping one `Arc`.
    pub fn refresh_scope(&mut self, globals: OwnedGlobals) {
        if let Some(scope) = &mut self.scope {
            scope.globals = globals;
        }
    }

    /// Drop this frame's store snapshot while it is not executing (its callee
    /// is). A held snapshot pins the store version at frame entry, and every
    /// pinned version forces the next COW mutation of a global container to
    /// deep-copy — O(recursion depth x container) memory under the parser.
    /// The frame re-acquires a snapshot through `refresh_scope` at sync.
    pub fn release_scope(&mut self) {
        if let Some(scope) = &mut self.scope {
            scope.globals = EMPTY_GLOBALS.with(Arc::clone);
        }
    }

    /// Get a mutable reference to a value, promoting it from the shared
    /// base/scope into the local overlay on first mutable access (so the
    /// shared layers stay immutable). Enables in-place mutation of
    /// arrays/dicts held in a local or `self`, avoiding an O(n) copy-on-write
    /// clone per element write. Copy-on-write semantics are preserved: the
    /// promoted value Arc-clones the container handle, so a genuinely aliased
    /// container still deep-copies on the first `Arc::make_mut` and only then
    /// mutates in place.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        if self.overlay.contains_key(key) {
            self.refreshed_globals.remove(key);
            self.dirty_names.insert(key.to_string());
            return self.overlay.get_mut(key);
        }
        if self.tombstones.contains(key) {
            return None;
        }
        let promoted = self.get(key).cloned();
        if let Some(v) = promoted {
            self.overlay.insert(key.to_string(), v);
            self.refreshed_globals.remove(key);
            self.dirty_names.insert(key.to_string());
            return self.overlay.get_mut(key);
        }
        None
    }

    fn shared_contains(&self, key: &str) -> bool {
        self.scope
            .as_ref()
            .is_some_and(|scope| scope.contains_live(key) || scope.contains_static(key))
            || self.base.as_ref().is_some_and(|base| base.contains_key(key))
    }

    /// Remove a key. Returns the removed value if any.
    pub fn remove(&mut self, key: &str) -> Option<Value> {
        self.refreshed_globals.remove(key);
        if let Some(v) = self.overlay.remove(key) {
            // If the key also exists in a shared layer, add a tombstone so we don't see it
            if self.shared_contains(key) {
                self.tombstones.insert(key.to_string());
            }
            return Some(v);
        }
        if self.tombstones.contains(key) {
            return None;
        }
        let shared = self.get(key).cloned();
        if shared.is_some() {
            self.tombstones.insert(key.to_string());
        }
        shared
    }

    /// Check if a key exists in the environment.
    pub fn contains_key(&self, key: &str) -> bool {
        if self.overlay.contains_key(key) {
            return true;
        }
        if self.tombstones.contains(key) {
            return false;
        }
        self.shared_contains(key)
    }

    /// All visible (key, value) pairs, first-wins in lookup precedence:
    /// overlay, live scope, base, static module env; tombstones hide the
    /// shared layers.
    fn visible_entries<'a>(&'a self) -> Vec<(&'a String, &'a Value)> {
        let mut out: Vec<(&'a String, &'a Value)> = Vec::with_capacity(self.overlay.len());
        let mut seen: HashSet<&'a str> = HashSet::with_capacity(self.overlay.len());
        for (k, v) in &self.overlay {
            seen.insert(k.as_str());
            out.push((k, v));
        }
        let tombstones = &self.tombstones;
        let mut push_shared = |k: &'a String, v: &'a Value| {
            if !tombstones.contains(k.as_str()) && seen.insert(k.as_str()) {
                out.push((k, v));
            }
        };
        if let Some(scope) = &self.scope {
            scope.for_each_live(&mut push_shared);
        }
        if let Some(base) = &self.base {
            for (k, v) in base.iter() {
                push_shared(k, v);
            }
        }
        if let Some(env) = self.scope.as_ref().and_then(|scope| scope.module_env.as_ref()) {
            for (k, v) in env.iter() {
                push_shared(k, v);
            }
        }
        out
    }

    /// Number of visible entries.
    pub fn len(&self) -> usize {
        self.visible_entries().len()
    }

    /// The `Arc` whose address `template_key` reports, when this env has one.
    /// The template cache holds a `Weak` clone of it and verifies identity on
    /// every hit: `template_key` is a raw ADDRESS, and an address is reusable
    /// once the allocation dies, so a key alone admits an ABA hit on a
    /// different env that happens to land at the same address. A `Weak` keeps
    /// the allocation (not its contents) alive, so the address cannot be
    /// recycled while the entry exists, and a dead base fails `upgrade()`.
    /// Returns `None` for both "no base" and "not a template-able env" --
    /// callers pair it with `template_key`, which distinguishes the two.
    pub fn template_base(&self) -> Option<Arc<HashMap<String, Value>>> {
        if !self.overlay.is_empty() || !self.tombstones.is_empty() {
            return None;
        }
        self.base.clone()
    }

    /// Check if the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.visible_entries().is_empty()
    }

    /// Iterate over all keys (merged, deduplicated).
    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.iter().map(|(k, _)| k)
    }

    /// Iterate over all values (merged).
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.iter().map(|(_, v)| v)
    }

    /// Iterate over all (key, value) pairs (merged).
    pub fn iter(&self) -> std::vec::IntoIter<(&String, &Value)> {
        self.visible_entries().into_iter()
    }

    /// True when this frame holds its own copy of `name` (written, bound, or
    /// refreshed here), as opposed to reading it through a shared layer.
    pub fn has_overlay_entry(&self, name: &str) -> bool {
        self.overlay.contains_key(name)
    }

    /// Iterate over values written in this environment frame.
    pub fn overlay_entries(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.overlay.iter()
    }

    /// Extend the overlay with entries from an iterator.
    pub fn extend<I: IntoIterator<Item = (String, Value)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }

    /// Refresh globals after a callee without marking them as caller writes.
    pub fn refresh_globals<I: IntoIterator<Item = (String, Value)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.tombstones.remove(&key);
            self.overlay.insert(key.clone(), value);
            self.refreshed_globals.insert(key);
        }
    }

    pub fn is_refreshed_global(&self, name: &str) -> bool {
        self.refreshed_globals.contains(name)
    }

    /// Overlay entries that were refreshed from the global store (callee
    /// sync), as opposed to written by this frame.
    pub fn refreshed_global_entries(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.overlay
            .iter()
            .filter(|(name, _)| self.refreshed_globals.contains(name.as_str()))
    }

    pub fn forward_globals<I: IntoIterator<Item = (String, Value)>>(&mut self, owner: Arc<str>, iter: I) {
        for (name, value) in iter {
            self.forwarded_globals.insert((Arc::clone(&owner), name), value);
        }
    }

    pub fn forwarded_globals(&self) -> impl Iterator<Item = (&(Arc<str>, String), &Value)> {
        self.forwarded_globals.iter()
    }

    pub fn bind_global(&mut self, local_name: String, owner: Arc<str>, source_name: String) {
        if !self.is_local(&local_name) {
            Arc::make_mut(&mut self.global_bindings).insert(local_name, (owner, source_name));
        }
    }

    /// (defining owner, defining name) behind `local_name`: an explicit
    /// binding first, otherwise the module scope — unless the name is a local
    /// of this frame, which shadows any global.
    pub fn global_binding(&self, local_name: &str) -> Option<(Arc<str>, String)> {
        if let Some(binding) = self.global_bindings.get(local_name) {
            return Some(binding.clone());
        }
        if self.is_local(local_name) {
            return None;
        }
        self.scope.as_ref()?.binding(local_name)
    }

    /// Every (local name, (owner, source)) pair this frame treats as a global
    /// alias. Materialized — O(globals) — so only for diagnostics.
    pub fn global_bindings(&self) -> Vec<(String, (Arc<str>, String))> {
        let mut out: Vec<(String, (Arc<str>, String))> = self
            .global_bindings
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        if let Some(scope) = &self.scope {
            scope.for_each_binding(|name, binding| {
                if !self.is_local(name) && !self.global_bindings.contains_key(name) {
                    out.push((name.clone(), binding));
                }
            });
        }
        out
    }

    /// Names written through this frame since the last `clear_dirty()`.
    pub fn dirty_names(&self) -> impl Iterator<Item = &String> {
        self.dirty_names.iter()
    }

    /// Reset dirty tracking; call right after cloning an env into a frame so
    /// only writes made by that frame count as dirty.
    pub fn clear_dirty(&mut self) {
        self.dirty_names.clear();
    }

    /// Strict-mode only (plan M5 §3.2, "poison-on-free"/stale-state class):
    /// regression lock on the `copy_back_block_writes` invariant that broke
    /// once already (`block_exec.rs`, historical bug: copying every shared
    /// key instead of only `dirty_names` replayed a cloned block env's stale
    /// snapshot over values a deeper call had since written). The invariant
    /// is: every name recorded dirty must still be present in THIS env's own
    /// overlay (i.e. actually written by this frame, not merely inherited
    /// from a clone). Returns the first offending name, or `None` when the
    /// invariant holds. Callers gate the call itself on `strict_mem_enabled()`
    /// so the off-path never iterates `dirty_names`.
    pub fn check_dirty_names_invariant(&self) -> Option<&str> {
        for name in &self.dirty_names {
            if !self.overlay.contains_key(name) {
                return Some(name.as_str());
            }
        }
        None
    }

    /// Test-only escape hatch (see `value_tests_strict_mem.rs`) to construct
    /// exactly the violation shape `check_dirty_names_invariant` guards
    /// against, without needing to actually reintroduce the historical
    /// `copy_back_block_writes` bug in production code: mark a name dirty
    /// with no corresponding overlay entry.
    #[cfg(test)]
    pub(crate) fn test_mark_dirty_without_overlay(&mut self, name: &str) {
        self.dirty_names.insert(name.to_string());
    }

    /// Project a subset of names into a fresh env, preserving global-binding,
    /// local-binding and refreshed-global metadata, and the module scope.
    /// Selective lambda capture MUST use this instead of a plain name->value
    /// map: `from_map` demotes an imported global alias to a local-looking
    /// value, losing its defining owner — the exact metadata-loss path behind
    /// the stage-4 stale-arena reads.
    pub fn project_preserving_bindings(&self, names: &HashSet<String>) -> CowEnv {
        let mut env = CowEnv::new();
        env.scope = self.scope.clone();
        env.release_scope();
        for (k, v) in self.iter() {
            if names.contains(k.as_str()) {
                env.overlay.insert(k.clone(), v.clone());
            }
        }
        for (local_name, (owner, source_name)) in self.global_bindings.iter() {
            if names.contains(local_name.as_str()) {
                Arc::make_mut(&mut env.global_bindings)
                    .insert(local_name.clone(), (Arc::clone(owner), source_name.clone()));
            }
        }
        for name in &self.local_bindings {
            if names.contains(name.as_str()) {
                env.local_bindings.insert(name.clone());
            }
        }
        for name in self.block_local_bindings.keys() {
            if names.contains(name.as_str()) {
                env.local_bindings.insert(name.clone());
            }
        }
        for name in &self.refreshed_globals {
            if names.contains(name.as_str()) && env.overlay.contains_key(name.as_str()) {
                env.refreshed_globals.insert(name.clone());
            }
        }
        env
    }

    /// Make the live value of (`owner`, `source_name`) visible through every
    /// local alias of it. A stale copy sitting in this frame's overlay is
    /// overwritten (marked refreshed, not dirty); an alias not in the overlay
    /// already reads the value through the scope and needs nothing. Returns
    /// true when the global is visible in this frame at all.
    pub fn refresh_bound_global(&mut self, owner: &Arc<str>, source_name: &str, value: Value) -> bool {
        let mut local_names = self
            .global_bindings
            .iter()
            .filter(|(_, (bound_owner, bound_name))| bound_owner == owner && bound_name == source_name)
            .map(|(local_name, _)| local_name.clone())
            .collect::<Vec<_>>();
        if let Some(scope) = &self.scope {
            scope.aliases_of(owner, source_name, &mut local_names);
        }
        local_names.retain(|local_name| !self.is_local(local_name));
        let refreshed = !local_names.is_empty();
        if self.scope.is_some() {
            local_names.retain(|local_name| self.overlay.contains_key(local_name.as_str()));
        }
        self.refresh_globals(local_names.into_iter().map(|local_name| (local_name, value.clone())));
        refreshed
    }

    /// Create a CowEnv from an existing HashMap (map becomes the overlay).
    pub fn from_map(map: HashMap<String, Value>) -> Self {
        CowEnv {
            base: None,
            scope: None,
            overlay: map,
            tombstones: HashSet::new(),
            local_bindings: HashSet::new(),
            block_local_bindings: HashMap::new(),
            refreshed_globals: HashSet::new(),
            forwarded_globals: HashMap::new(),
            global_bindings: Arc::new(HashMap::new()),
            dirty_names: HashSet::new(),
            uninit_names: HashSet::new(),
        }
    }

    /// Create a CowEnv with a shared base (for function calls).
    pub fn with_base(base: Arc<HashMap<String, Value>>) -> Self {
        CowEnv {
            base: Some(base),
            scope: None,
            overlay: HashMap::new(),
            tombstones: HashSet::new(),
            local_bindings: HashSet::new(),
            block_local_bindings: HashMap::new(),
            refreshed_globals: HashSet::new(),
            forwarded_globals: HashMap::new(),
            global_bindings: Arc::new(HashMap::new()),
            dirty_names: HashSet::new(),
            uninit_names: HashSet::new(),
        }
    }

    /// Materialize into a flat HashMap (for cases that need it).
    pub fn to_map(&self) -> HashMap<String, Value> {
        self.visible_entries()
            .into_iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    /// Freeze current state into a shareable Arc<HashMap> for capture.
    pub fn freeze(&self) -> Arc<HashMap<String, Value>> {
        Arc::new(self.to_map())
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.overlay.clear();
        self.tombstones.clear();
        self.base = None;
        self.scope = None;
        self.refreshed_globals.clear();
        self.forwarded_globals.clear();
        self.local_bindings.clear();
        self.block_local_bindings.clear();
        self.global_bindings = Arc::new(HashMap::new());
        self.dirty_names.clear();
        self.uninit_names.clear();
    }

    /// Provide entry-like API by delegating to the overlay.
    /// If the key exists in a shared layer but not overlay, copy it to overlay first.
    pub fn entry(&mut self, key: String) -> std::collections::hash_map::Entry<'_, String, Value> {
        self.refreshed_globals.remove(&key);
        self.dirty_names.insert(key.clone());
        // If key is in a shared layer but not in overlay, promote it
        if !self.overlay.contains_key(&key) && !self.tombstones.contains(&key) {
            if let Some(v) = self.get(&key).cloned() {
                self.overlay.insert(key.clone(), v);
            }
        }
        self.tombstones.remove(&key);
        self.overlay.entry(key)
    }
}

impl Default for CowEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for CowEnv {
    fn clone(&self) -> Self {
        CowEnv {
            base: self.base.clone(),             // Arc::clone — O(1)
            scope: self.scope.clone(),           // four Arc::clones — O(1)
            overlay: self.overlay.clone(),       // small
            tombstones: self.tombstones.clone(), // small
            local_bindings: self.local_bindings.clone(),
            block_local_bindings: self.block_local_bindings.clone(),
            refreshed_globals: self.refreshed_globals.clone(),
            forwarded_globals: self.forwarded_globals.clone(),
            global_bindings: self.global_bindings.clone(),
            dirty_names: self.dirty_names.clone(),
            uninit_names: self.uninit_names.clone(),
        }
    }
}

impl PartialEq for CowEnv {
    fn eq(&self, other: &Self) -> bool {
        // Materialize and compare — used rarely (e.g., in Value::PartialEq)
        self.to_map() == other.to_map()
    }
}

impl IntoIterator for CowEnv {
    type Item = (String, Value);
    type IntoIter = std::collections::hash_map::IntoIter<String, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_map().into_iter()
    }
}

impl<'a> IntoIterator for &'a CowEnv {
    type Item = (&'a String, &'a Value);
    type IntoIter = std::vec::IntoIter<(&'a String, &'a Value)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl From<HashMap<String, Value>> for CowEnv {
    fn from(map: HashMap<String, Value>) -> Self {
        CowEnv::from_map(map)
    }
}

impl std::iter::FromIterator<(String, Value)> for CowEnv {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(iter: T) -> Self {
        CowEnv::from_map(iter.into_iter().collect())
    }
}

impl std::ops::Index<&str> for CowEnv {
    type Output = Value;
    fn index(&self, key: &str) -> &Value {
        self.get(key).expect("key not found in CowEnv")
    }
}

/// Variable environment for compile-time evaluation.
/// Now backed by CowEnv for O(1) clone at function call sites.
pub type Env = CowEnv;

thread_local! {
    pub(crate) static MANUAL_GC: ManualGc = ManualGc::new();
}

/// NewType for class/struct names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure ClassName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassName(pub String);

impl ClassName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for ClassName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for ClassName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum type names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure EnumTypeName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumTypeName(pub String);

impl EnumTypeName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for EnumTypeName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for EnumTypeName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum variant names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure VariantName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantName(pub String);

impl VariantName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for VariantName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for VariantName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

//==============================================================================
// Special Enum Types (for formal verification)
//==============================================================================
// These enums replace magic string comparisons for built-in enum types.
// This enables more precise verification and eliminates string-based dispatch.

/// Built-in enum types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumType
///   | option  -- Option<T> (Some/None)
///   | result  -- Result<T, E> (Ok/Err)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumType {
    /// Option type: Some(T) | None
    Option,
    /// Result type: Ok(T) | Err(E)
    Result,
}

impl SpecialEnumType {
    /// Try to parse an enum name as a special enum type.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            enum_names::OPTION => Some(SpecialEnumType::Option),
            enum_names::RESULT => Some(SpecialEnumType::Result),
            _ => None,
        }
    }

    /// Get the string name of this special enum type.
    pub fn as_str(&self) -> &'static str {
        match self {
            SpecialEnumType::Option => enum_names::OPTION,
            SpecialEnumType::Result => enum_names::RESULT,
        }
    }
}

/// Option enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive OptionVariant
///   | some
///   | none
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptionVariant {
    Some,
    None,
}

impl OptionVariant {
    /// Try to parse a variant name as an Option variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            enum_names::SOME => Some(OptionVariant::Some),
            enum_names::NONE => Some(OptionVariant::None),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            OptionVariant::Some => enum_names::SOME,
            OptionVariant::None => enum_names::NONE,
        }
    }
}

/// Result enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive ResultVariant
///   | ok
///   | err
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultVariant {
    Ok,
    Err,
}

impl ResultVariant {
    /// Try to parse a variant name as a Result variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            enum_names::OK => Some(ResultVariant::Ok),
            enum_names::ERR => Some(ResultVariant::Err),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            ResultVariant::Ok => enum_names::OK,
            ResultVariant::Err => enum_names::ERR,
        }
    }
}

/// Represents the kind of special enum value, combining type and variant.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumValue
///   | optionSome (payload : Value)
///   | optionNone
///   | resultOk (payload : Value)
///   | resultErr (payload : Value)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumKind {
    /// Option::Some
    OptionSome,
    /// Option::None
    OptionNone,
    /// Result::Ok
    ResultOk,
    /// Result::Err
    ResultErr,
}

impl SpecialEnumKind {
    /// Try to parse enum_name and variant as a special enum kind.
    pub fn from_names(enum_name: &str, variant: &str) -> Option<Self> {
        match (enum_name, variant) {
            ("Option", "Some") => Some(SpecialEnumKind::OptionSome),
            ("Option", "None") => Some(SpecialEnumKind::OptionNone),
            ("Result", "Ok") => Some(SpecialEnumKind::ResultOk),
            ("Result", "Err") => Some(SpecialEnumKind::ResultErr),
            _ => None,
        }
    }

    /// Check if this is an Option variant.
    pub fn is_option(&self) -> bool {
        matches!(self, SpecialEnumKind::OptionSome | SpecialEnumKind::OptionNone)
    }

    /// Check if this is a Result variant.
    pub fn is_result(&self) -> bool {
        matches!(self, SpecialEnumKind::ResultOk | SpecialEnumKind::ResultErr)
    }
}

/// Shared-identity class instance storage (source `class` values).
#[derive(Debug)]
pub struct ClassInstance {
    class: String,
    fields: RwLock<HashMap<String, Value>>,
}

impl ClassInstance {
    pub fn new(class: String, fields: HashMap<String, Value>) -> Self {
        Self {
            class,
            fields: RwLock::new(fields),
        }
    }

    pub fn class(&self) -> &str {
        &self.class
    }

    pub fn field(&self, name: &str) -> Option<Value> {
        self.fields.read().unwrap().get(name).cloned()
    }

    pub fn set_field(&self, name: String, value: Value) {
        self.fields.write().unwrap().insert(name, value);
    }

    /// Mutate a field's value in place under the write lock. Returns None
    /// when the field does not exist. Used by indexed field assignment
    /// (`obj.field[i] = v`) so hot raster loops avoid cloning the container
    /// on every write.
    pub fn field_mut<R>(&self, name: &str, f: impl FnOnce(&mut Value) -> R) -> Option<R> {
        self.fields.write().unwrap().get_mut(name).map(f)
    }

    pub fn fields_snapshot(&self) -> HashMap<String, Value> {
        self.fields.read().unwrap().clone()
    }
}

/// Runtime value representation.
#[derive(Debug)]
pub enum Value {
    Int(i64),
    /// Unsigned integer with explicit bit width (8/16/32/64).
    /// Carries width so arithmetic ops can apply modulo-2^width wrap.
    /// `value` stores the unsigned value zero-extended into u64.
    UInt {
        value: u64,
        width: u8, // 8, 16, 32, or 64
    },
    Float(f64),
    /// Single-precision float (`f32`).
    ///
    /// Carries native `f32` storage so arithmetic preserves IEEE 754 single-precision
    /// rounding. Without this variant, values typed `f32` were silently promoted to
    /// `f64`, producing wrong results like `0.1f32 + 0.2f32 - 0.3f32 == 5.55e-17`
    /// (the f64 error) instead of the correct `0.0f32`.
    ///
    /// Mirrors the W5-I `Value::UInt { value, width }` width-tag pattern — but uses a
    /// dedicated variant rather than a width tag because storing an `f32` value in an
    /// `f64` slot would introduce double rounding at literal parse time.
    Float32(f32),
    Bool(bool),
    Str(SharedText),
    /// Text carrying raw bytes that are not valid UTF-8 on their own.
    /// Produced ONLY by byte-indexed text slicing that splits a multi-byte
    /// codepoint (s[i:i+1] walks). The compiled lane's text is raw bytes, so
    /// a mid-codepoint fragment must survive reassembly: concatenation and
    /// join re-validate and collapse back to `Str` the moment the joined
    /// bytes form valid UTF-8. Substituting U+FFFD at slice time instead
    /// (the previous behavior) shredded every fragment-reassembly parser —
    /// see doc/09_report/seed_redeploy_readiness_2026-07-30.md (the NO-GO
    /// blocker). Display/keying boundaries may render it lossily; equality
    /// and length are byte-wise.
    StrBytes(Arc<Vec<u8>>),
    Symbol(String),
    /// Mutable array (default for array literals)
    /// Wrapped in Arc for O(1) clone (COW via Arc::make_mut for mutations)
    Array(Arc<Vec<Value>>),
    /// Packed mutable `[u8]` storage. Mutations use `Arc::make_mut` COW.
    ByteArray(Arc<Vec<u8>>),
    /// Immutable frozen array (created via freeze(), copy-on-freeze semantics)
    FrozenArray(Arc<Vec<Value>>),
    /// Packed immutable `[u8]` storage.
    FrozenByteArray(Arc<Vec<u8>>),
    /// Fixed-size array with runtime size checking ([T; N] syntax)
    /// Rejects size-changing operations (push, pop, insert, remove, clear)
    FixedSizeArray {
        size: usize,
        data: Vec<Value>,
    },
    Tuple(Vec<Value>),
    /// Tuple with field labels preserved for runtime field access and display.
    ///
    /// Storage remains positional; labels are metadata paired with values.
    LabeledTuple {
        labels: Vec<String>,
        values: Vec<Value>,
    },
    /// Mutable dict (default for dict literals)
    Dict(Arc<HashMap<String, Value>>),
    /// Immutable frozen dict (created via freeze(), copy-on-freeze semantics)
    FrozenDict(Arc<HashMap<String, Value>>),
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
        env: Arc<Env>,
    },
    /// A block closure - used for BDD DSL colon-blocks like `describe "name": body`
    /// Contains a list of statements to execute when called
    BlockClosure {
        nodes: Vec<Node>,
        env: Arc<Env>,
    },
    /// A function reference - used for decorators and first-class functions
    /// Includes captured environment for closure semantics
    Function {
        name: String,
        def: Arc<FunctionDef>,
        captured_env: Arc<Env>,
    },
    Object {
        class: String,
        fields: Arc<HashMap<String, Value>>,
    },
    /// A source `class` value. Clones share this identity cell, unlike the
    /// copy-on-write `Object` carrier used by source `struct` values.
    ClassInstance(Arc<ClassInstance>),
    Enum {
        enum_name: String,
        variant: String,
        payload: Option<Box<Value>>,
    },
    /// Union type value - wraps a value with its type index
    /// Represents values of union types like `str | i64`
    Union {
        /// Index of the actual type in the union's variant list
        type_index: usize,
        /// The actual value
        inner: Box<Value>,
    },
    /// Constructor reference - a class that can be used to create instances
    /// Used for constructor polymorphism: Constructor[T] type
    Constructor {
        class_name: String,
    },
    /// Enum type reference - allows EnumName.VariantName syntax
    /// Used for enum variant construction: Color.Red, Option.Some(x)
    EnumType {
        enum_name: String,
    },
    /// Trait type reference - represents a trait definition
    /// Used for trait exports and "impl Trait for Type" syntax
    TraitType {
        trait_name: String,
    },
    /// Enum variant constructor - callable to create enum with payload
    /// Used for variants with data: Option.Some(x), Result.Ok(value)
    EnumVariantConstructor {
        enum_name: String,
        variant_name: String,
    },
    /// Dynamic trait object - wraps a value with its trait for dynamic dispatch
    /// Enables polymorphism via trait implementations (dyn Trait syntax)
    TraitObject {
        trait_name: String,
        inner: Box<Value>,
    },
    /// Unit value - wraps a numeric value with its unit suffix
    /// Enables type-safe unit arithmetic and conversion methods
    Unit {
        value: Box<Value>,
        suffix: String,
        family: Option<String>, // Name of unit family for conversions
    },
    Actor(ActorHandle),
    Future(FutureValue),
    Generator(GeneratorValue),
    Channel(ChannelValue),
    ThreadPool(ThreadPoolValue),
    Unique(ManualUniqueValue),
    Shared(ManualSharedValue),
    Weak(ManualWeakValue),
    Handle(ManualHandleValue),
    Borrow(BorrowValue),
    BorrowMut(BorrowMutValue),
    /// Mock object for testing - stores method configurations and call records
    Mock(MockValue),
    /// Argument matcher for mock verification
    Matcher(MatcherValue),
    /// Native callable for interpreter intrinsics (internal use only).
    NativeFunction(NativeFunction),
    /// Custom block value - result of evaluating m{}, sh{}, sql{}, re{}, etc.
    /// Stores the block kind and payload for block-specific processing.
    Block {
        kind: String,               // Block kind: "m", "sh", "sql", "re", "md", "html", "graph", "img"
        payload: String,            // Raw payload content
        result: Option<Box<Value>>, // Parsed/evaluated result (lazily computed)
    },
    Nil,
}

/// Boxed native function callable from the interpreter.
pub type NativeFnArc = Arc<dyn Fn(&[Value]) -> Result<Value, CompileError> + Send + Sync>;

pub struct NativeFunction {
    pub name: String,
    pub func: NativeFnArc,
}

impl fmt::Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeFunction({})", self.name)
    }
}

impl Clone for NativeFunction {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            func: Arc::clone(&self.func),
        }
    }
}

impl Value {
    /// Construct an aggregate (`struct` or `class`) instance value.
    ///
    /// Both value types (`struct`) and reference types (`class`) currently build
    /// `Value::Object`. `981c88435e0` routed `is_value_type == false` to
    /// `Value::ClassInstance`, but neither primary resolution path has a
    /// `ClassInstance` arm — field access (`interpreter/expr/calls.rs`) and method
    /// dispatch (`interpreter_method/mod.rs`) both only match `Value::Object` —
    /// so every interpreted `class` field read and method call failed with
    /// "not found on type `object`".
    ///
    /// TODO(class-instance): re-land reference-class identity via
    /// `Value::ClassInstance` only together with `ClassInstance` arms in BOTH
    /// primary resolution paths plus an audit of the remaining `Value::Object`
    /// pattern matches in the interpreter. See
    /// `doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md`.
    pub fn aggregate(class: String, fields: HashMap<String, Value>, _is_value_type: bool) -> Self {
        Value::Object {
            class,
            fields: Arc::new(fields),
        }
    }

    pub fn aggregate_class(&self) -> Option<&str> {
        match self {
            Value::Object { class, .. } => Some(class),
            Value::ClassInstance(instance) => Some(instance.class()),
            _ => None,
        }
    }

    pub fn aggregate_field(&self, name: &str) -> Option<Value> {
        match self {
            Value::Object { fields, .. } => fields.get(name).cloned(),
            Value::ClassInstance(instance) => instance.field(name),
            _ => None,
        }
    }

    pub fn text(value: impl Into<String>) -> Self {
        Value::Str(Arc::new(value.into()))
    }

    pub fn shared_text(value: SharedText) -> Self {
        Value::Str(value)
    }

    pub fn text_owned(value: String) -> Self {
        Value::text(value)
    }

    pub fn as_text_str(&self) -> Option<&str> {
        match self {
            Value::Str(value) => Some(value.as_str()),
            Value::Symbol(value) => Some(value.as_str()),
            _ => None,
        }
    }

    pub fn into_text_string(self) -> Option<String> {
        match self {
            Value::Str(value) => Some(Arc::try_unwrap(value).unwrap_or_else(|value| value.as_ref().clone())),
            Value::Symbol(value) => Some(value),
            _ => None,
        }
    }

    /// Create a new mutable array value (default for array literals)
    pub fn array(vec: Vec<Value>) -> Self {
        Value::Array(Arc::new(vec))
    }

    pub fn byte_array(vec: Vec<u8>) -> Self {
        Value::ByteArray(Arc::new(vec))
    }

    /// Create a new frozen (immutable) array value
    pub fn frozen_array(vec: Vec<Value>) -> Self {
        Value::FrozenArray(Arc::new(vec))
    }

    pub fn frozen_byte_array(vec: Vec<u8>) -> Self {
        Value::FrozenByteArray(Arc::new(vec))
    }

    /// Borrow packed byte storage without confusing it with raw text bytes.
    pub fn byte_array_view(&self) -> Option<&[u8]> {
        match self {
            Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => Some(bytes.as_slice()),
            _ => None,
        }
    }

    /// Widen packed bytes to ordinary interpreter values at a generic-array boundary.
    pub fn byte_array_values(bytes: &[u8]) -> Vec<Value> {
        bytes
            .iter()
            .map(|byte| Value::UInt {
                value: u64::from(*byte),
                width: 8,
            })
            .collect()
    }

    /// Extract `[u8]` semantics from packed or legacy boxed array storage.
    pub fn try_array_bytes(&self) -> Option<Vec<u8>> {
        if let Some(bytes) = self.byte_array_view() {
            return Some(bytes.to_vec());
        }
        let values = match self {
            Value::Array(values) | Value::FrozenArray(values) => values.as_slice(),
            Value::FixedSizeArray { data, .. } => data.as_slice(),
            _ => return None,
        };
        values
            .iter()
            .map(|value| match value {
                Value::UInt { value, .. } => u8::try_from(*value).ok(),
                Value::Int(value) => u8::try_from(*value).ok(),
                _ => None,
            })
            .collect()
    }

    /// Create a new mutable dict value (default for dict literals)
    pub fn dict(map: HashMap<String, Value>) -> Self {
        Value::Dict(Arc::new(map))
    }

    /// Create a new frozen (immutable) dict value
    pub fn frozen_dict(map: HashMap<String, Value>) -> Self {
        Value::FrozenDict(Arc::new(map))
    }

    /// True if this value is "nil-like": either the bare `nil` literal
    /// (`Value::Nil`) or an `Option::None` enum.
    ///
    /// These two share semantics ("absence of a value") but have distinct
    /// runtime representations: a `nil` literal evaluates to `Value::Nil`,
    /// while a function declared to return `T?` that does `return nil` yields
    /// `Option::None` (a `Value::Enum`). Equality (`==` / `!=`) against the
    /// `nil` literal must treat both as equal, so callers like
    /// `if opt != nil:` work regardless of which representation `opt` holds.
    /// `Result::Err`/`Result::Ok` and `Option::Some(_)` are NOT nil-like.
    pub fn is_nil_like(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Enum { enum_name, variant, .. } => enum_name == enum_names::OPTION && variant == enum_names::NONE,
            _ => false,
        }
    }

    /// Unwrap a single-payload `Option::Some(x)` down to `x`; any other value is
    /// returned unchanged.
    ///
    /// A nullable `T?` has two runtime representations, exactly like the
    /// nil/`Option::None` split documented on [`Value::is_nil_like`]: a literal
    /// `7` assigned to a `T?` stays a bare `Value::Int`, while a function
    /// declared `-> i64?` that returns `7` yields `Option::Some(7)`
    /// (a `Value::Enum`). Equality must bridge those, or `opt == 7` is
    /// unconditionally false for the function-returned form.
    pub fn unwrap_option_payload(&self) -> &Value {
        match self {
            Value::Enum {
                enum_name,
                variant,
                payload: Some(inner),
            } if enum_name == enum_names::OPTION && variant == enum_names::SOME => inner.as_ref(),
            _ => self,
        }
    }

    /// Equality with nullable (`T?`) semantics — the single source of truth for
    /// `==`/`!=` on values that may be Option-wrapped.
    ///
    /// Bridges BOTH representation splits a nullable can present:
    /// - `nil` literal vs `Option::None` (see [`Value::is_nil_like`])
    /// - a bare payload vs `Option::Some(payload)`
    ///
    /// Without the second bridge every `expect(f()).to_equal(v)` on a function
    /// returning `T?` compares `Option::Some(v)` against `v` and reports a
    /// FALSE FAILURE, while `to_not_equal(v)` reports a FALSE PASS.
    pub fn nullable_eq(&self, other: &Value) -> bool {
        if self.is_nil_like() || other.is_nil_like() {
            return self.is_nil_like() && other.is_nil_like();
        }
        self.unwrap_option_payload() == other.unwrap_option_payload()
    }

    /// Create a new fixed-size array with runtime size checking
    /// Returns error if data length doesn't match expected size
    pub fn fixed_size_array(size: usize, data: Vec<Value>) -> Result<Self, String> {
        if data.len() != size {
            return Err(format!(
                "Fixed-size array size mismatch: expected {}, got {}",
                size,
                data.len()
            ));
        }
        Ok(Value::FixedSizeArray { size, data })
    }
}

// Value implementation methods
include!("value_impl.rs");

// Pointer wrappers (Manual memory management, Borrow types)
include!("value_pointers.rs");

// Include tests from separate file
include!("value_tests.rs");
