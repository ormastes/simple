# Dynamic Reload Plan

## Overview

Implement hot-reloading capability for Simple modules. This allows code changes to take effect without restarting the application, enabling rapid iteration during development.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     Hot Reload System                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────┐         ┌──────────────┐                          │
│  │  File Watcher │────────▶│  Compiler    │                          │
│  │  (notify)     │         │  (AOT)       │                          │
│  └──────────────┘         └──────┬───────┘                          │
│                                  │                                   │
│                                  ▼                                   │
│  ┌──────────────────────────────────────────────────────────┐       │
│  │                    Reload Manager                         │       │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────────┐      │       │
│  │  │  Version   │  │  Symbol    │  │  State         │      │       │
│  │  │  Tracker   │  │  Patcher   │  │  Migration     │      │       │
│  │  └────────────┘  └────────────┘  └────────────────┘      │       │
│  └──────────────────────────────────────────────────────────┘       │
│                                  │                                   │
│                                  ▼                                   │
│  ┌──────────────────────────────────────────────────────────┐       │
│  │                    Runtime                                │       │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────────┐      │       │
│  │  │  Trampoline│  │  Old Code  │  │  New Code      │      │       │
│  │  │  Table     │  │  (GC later)│  │  (active)      │      │       │
│  │  └────────────┘  └────────────┘  └────────────────┘      │       │
│  └──────────────────────────────────────────────────────────┘       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/hotreload/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── watcher.rs          # File system watcher
    ├── manager.rs          # Reload coordinator
    ├── version.rs          # Version tracking
    ├── trampoline.rs       # Function trampolines
    ├── patcher.rs          # Symbol patching
    └── migration.rs        # State migration
```

---

## Trampoline Table

The key to hot-reloading is **indirect function calls** through a trampoline table. Instead of calling functions directly, code calls through a table that can be updated atomically.

### Trampoline Implementation (trampoline.rs)

```rust
// crates/hotreload/src/trampoline.rs

use std::sync::atomic::{AtomicUsize, Ordering};
use std::collections::HashMap;

/// Function pointer type
pub type FnPtr = *const ();

/// Trampoline table for hot-reloadable functions
pub struct TrampolineTable {
    /// Function pointers indexed by function ID
    entries: Vec<AtomicUsize>,
    /// Map function name to ID
    name_to_id: HashMap<String, usize>,
    /// Current capacity
    capacity: usize,
}

impl TrampolineTable {
    pub fn new(initial_capacity: usize) -> Self {
        let mut entries = Vec::with_capacity(initial_capacity);
        for _ in 0..initial_capacity {
            entries.push(AtomicUsize::new(0));
        }

        Self {
            entries,
            name_to_id: HashMap::new(),
            capacity: initial_capacity,
        }
    }

    /// Register a function, returns its ID
    pub fn register(&mut self, name: &str, ptr: FnPtr) -> usize {
        if let Some(&id) = self.name_to_id.get(name) {
            // Update existing entry
            self.entries[id].store(ptr as usize, Ordering::Release);
            return id;
        }

        // Allocate new entry
        let id = self.name_to_id.len();
        if id >= self.capacity {
            self.grow();
        }

        self.entries[id].store(ptr as usize, Ordering::Release);
        self.name_to_id.insert(name.to_string(), id);
        id
    }

    /// Update a function pointer atomically
    pub fn update(&self, id: usize, new_ptr: FnPtr) {
        self.entries[id].store(new_ptr as usize, Ordering::Release);
    }

    /// Update by name
    pub fn update_by_name(&self, name: &str, new_ptr: FnPtr) -> Option<()> {
        let id = *self.name_to_id.get(name)?;
        self.update(id, new_ptr);
        Some(())
    }

    /// Get current function pointer
    pub fn get(&self, id: usize) -> FnPtr {
        self.entries[id].load(Ordering::Acquire) as FnPtr
    }

    /// Get by name
    pub fn get_by_name(&self, name: &str) -> Option<FnPtr> {
        let id = *self.name_to_id.get(name)?;
        Some(self.get(id))
    }

    /// Get function ID
    pub fn get_id(&self, name: &str) -> Option<usize> {
        self.name_to_id.get(name).copied()
    }

    fn grow(&mut self) {
        let new_capacity = self.capacity * 2;
        for _ in self.capacity..new_capacity {
            self.entries.push(AtomicUsize::new(0));
        }
        self.capacity = new_capacity;
    }
}

// Thread-safe global trampoline table
lazy_static::lazy_static! {
    pub static ref TRAMPOLINES: std::sync::RwLock<TrampolineTable> =
        std::sync::RwLock::new(TrampolineTable::new(1024));
}

/// Call a reloadable function by ID
#[inline]
pub unsafe fn call_trampoline<F, R>(id: usize, f: impl FnOnce(F) -> R) -> R
where
    F: Copy,
{
    let table = TRAMPOLINES.read().unwrap();
    let ptr = table.get(id);
    let func: F = std::mem::transmute_copy(&ptr);
    f(func)
}

/// Generated trampoline stub (example for x86_64)
/// This would be generated by the compiler for each reloadable function
#[cfg(target_arch = "x86_64")]
pub fn generate_trampoline_stub(table_offset: usize) -> Vec<u8> {
    // mov rax, [rip + table_offset]  ; Load function pointer from table
    // jmp rax                        ; Jump to actual function

    let mut code = Vec::new();

    // LEA to get table address (simplified - would use actual table address)
    // This is placeholder - real implementation would use proper addressing
    code.extend_from_slice(&[
        0x48, 0x8B, 0x05,  // mov rax, [rip + disp32]
    ]);
    code.extend_from_slice(&(table_offset as i32).to_le_bytes());

    // JMP rax
    code.extend_from_slice(&[0xFF, 0xE0]);

    code
}
```

---

## Version Tracking

### Version Manager (version.rs)

```rust
// crates/hotreload/src/version.rs

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

/// Tracks module and function versions for reload safety
pub struct VersionTracker {
    /// Module versions: module_name -> version
    module_versions: HashMap<String, AtomicU64>,
    /// Function versions: (module, function) -> version
    function_versions: HashMap<(String, String), AtomicU64>,
    /// Type layout hashes: type_name -> hash
    type_layouts: HashMap<String, u64>,
}

impl VersionTracker {
    pub fn new() -> Self {
        Self {
            module_versions: HashMap::new(),
            function_versions: HashMap::new(),
            type_layouts: HashMap::new(),
        }
    }

    /// Increment module version
    pub fn bump_module(&self, module: &str) -> u64 {
        if let Some(v) = self.module_versions.get(module) {
            v.fetch_add(1, Ordering::SeqCst) + 1
        } else {
            1
        }
    }

    /// Get current module version
    pub fn module_version(&self, module: &str) -> u64 {
        self.module_versions
            .get(module)
            .map(|v| v.load(Ordering::SeqCst))
            .unwrap_or(0)
    }

    /// Check if type layout changed (breaking change)
    pub fn type_layout_changed(&self, type_name: &str, new_hash: u64) -> bool {
        if let Some(&old_hash) = self.type_layouts.get(type_name) {
            old_hash != new_hash
        } else {
            false  // New type, no change
        }
    }

    /// Update type layout
    pub fn update_type_layout(&mut self, type_name: &str, hash: u64) {
        self.type_layouts.insert(type_name.to_string(), hash);
    }

    /// Register new module
    pub fn register_module(&mut self, module: &str) {
        self.module_versions
            .entry(module.to_string())
            .or_insert_with(|| AtomicU64::new(1));
    }
}

/// Calculate layout hash for a type
pub fn calculate_layout_hash(type_info: &TypeInfo) -> u64 {
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;

    let mut hasher = DefaultHasher::new();

    // Hash size and alignment
    type_info.size.hash(&mut hasher);
    type_info.alignment.hash(&mut hasher);

    // Hash field layout
    for field in &type_info.fields {
        field.name.hash(&mut hasher);
        field.offset.hash(&mut hasher);
        field.type_id.hash(&mut hasher);
    }

    hasher.finish()
}

#[derive(Debug)]
pub struct TypeInfo {
    pub name: String,
    pub size: usize,
    pub alignment: usize,
    pub fields: Vec<FieldInfo>,
}

#[derive(Debug)]
pub struct FieldInfo {
    pub name: String,
    pub offset: usize,
    pub type_id: u32,
}
```

---

## File Watcher

### Watcher Implementation (watcher.rs)

```rust
// crates/hotreload/src/watcher.rs

use notify::{Watcher, RecursiveMode, Event, EventKind};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::time::{Duration, Instant};
use std::collections::HashMap;

/// File change event
#[derive(Debug, Clone)]
pub struct FileChange {
    pub path: PathBuf,
    pub kind: ChangeKind,
}

#[derive(Debug, Clone, Copy)]
pub enum ChangeKind {
    Modified,
    Created,
    Deleted,
}

/// Watches source files for changes
pub struct FileWatcher {
    watcher: notify::RecommendedWatcher,
    receiver: Receiver<FileChange>,
    /// Debounce: path -> last change time
    debounce: HashMap<PathBuf, Instant>,
    debounce_duration: Duration,
}

impl FileWatcher {
    pub fn new(debounce_ms: u64) -> Result<Self, notify::Error> {
        let (tx, rx) = channel();

        let sender = tx.clone();
        let watcher = notify::recommended_watcher(move |res: Result<Event, _>| {
            if let Ok(event) = res {
                let kind = match event.kind {
                    EventKind::Create(_) => Some(ChangeKind::Created),
                    EventKind::Modify(_) => Some(ChangeKind::Modified),
                    EventKind::Remove(_) => Some(ChangeKind::Deleted),
                    _ => None,
                };

                if let Some(kind) = kind {
                    for path in event.paths {
                        if path.extension().map(|e| e == "simple").unwrap_or(false) {
                            let _ = sender.send(FileChange { path, kind });
                        }
                    }
                }
            }
        })?;

        Ok(Self {
            watcher,
            receiver: rx,
            debounce: HashMap::new(),
            debounce_duration: Duration::from_millis(debounce_ms),
        })
    }

    /// Watch a directory for changes
    pub fn watch(&mut self, path: &Path) -> Result<(), notify::Error> {
        self.watcher.watch(path, RecursiveMode::Recursive)
    }

    /// Stop watching a directory
    pub fn unwatch(&mut self, path: &Path) -> Result<(), notify::Error> {
        self.watcher.unwatch(path)
    }

    /// Poll for file changes (non-blocking)
    pub fn poll(&mut self) -> Vec<FileChange> {
        let mut changes = Vec::new();
        let now = Instant::now();

        while let Ok(change) = self.receiver.try_recv() {
            // Debounce: ignore rapid successive changes
            if let Some(last) = self.debounce.get(&change.path) {
                if now.duration_since(*last) < self.debounce_duration {
                    continue;
                }
            }

            self.debounce.insert(change.path.clone(), now);
            changes.push(change);
        }

        // Clean old debounce entries
        self.debounce.retain(|_, time| {
            now.duration_since(*time) < self.debounce_duration * 10
        });

        changes
    }

    /// Block until a change occurs
    pub fn wait(&mut self) -> FileChange {
        loop {
            match self.receiver.recv_timeout(Duration::from_millis(100)) {
                Ok(change) => {
                    let now = Instant::now();
                    if let Some(last) = self.debounce.get(&change.path) {
                        if now.duration_since(*last) < self.debounce_duration {
                            continue;
                        }
                    }
                    self.debounce.insert(change.path.clone(), now);
                    return change;
                }
                Err(_) => continue,
            }
        }
    }
}
```

---

## Reload Manager

### Manager Implementation (manager.rs)

```rust
// crates/hotreload/src/manager.rs

use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};
use std::collections::HashMap;

use crate::watcher::{FileWatcher, FileChange, ChangeKind};
use crate::version::VersionTracker;
use crate::trampoline::TRAMPOLINES;
use crate::patcher::SymbolPatcher;
use crate::migration::StateMigrator;

use simple_compiler::CompilerPipeline;
use simple_loader::{ModuleRegistry, LoadedModule};

/// Manages hot-reloading of Simple modules
pub struct ReloadManager {
    /// Watched directories
    watched_dirs: Vec<PathBuf>,
    /// File watcher
    watcher: FileWatcher,
    /// Module registry
    modules: Arc<ModuleRegistry>,
    /// Version tracker
    versions: Arc<RwLock<VersionTracker>>,
    /// Compiler pipeline
    compiler: CompilerPipeline,
    /// Symbol patcher
    patcher: SymbolPatcher,
    /// State migrator
    migrator: StateMigrator,
    /// Source to output path mapping
    source_map: HashMap<PathBuf, PathBuf>,
    /// Reload callbacks
    on_reload: Vec<Box<dyn Fn(&str) + Send + Sync>>,
    /// Error callbacks
    on_error: Vec<Box<dyn Fn(&str, &str) + Send + Sync>>,
}

impl ReloadManager {
    pub fn new(modules: Arc<ModuleRegistry>) -> Result<Self, String> {
        Ok(Self {
            watched_dirs: Vec::new(),
            watcher: FileWatcher::new(100).map_err(|e| e.to_string())?,
            modules,
            versions: Arc::new(RwLock::new(VersionTracker::new())),
            compiler: CompilerPipeline::new()?,
            patcher: SymbolPatcher::new(),
            migrator: StateMigrator::new(),
            source_map: HashMap::new(),
            on_reload: Vec::new(),
            on_error: Vec::new(),
        })
    }

    /// Watch a source directory
    pub fn watch(&mut self, dir: &Path) -> Result<(), String> {
        self.watcher.watch(dir).map_err(|e| e.to_string())?;
        self.watched_dirs.push(dir.to_path_buf());
        Ok(())
    }

    /// Register source -> output mapping
    pub fn map_source(&mut self, source: PathBuf, output: PathBuf) {
        self.source_map.insert(source, output);
    }

    /// Register reload callback
    pub fn on_reload<F>(&mut self, callback: F)
    where
        F: Fn(&str) + Send + Sync + 'static,
    {
        self.on_reload.push(Box::new(callback));
    }

    /// Register error callback
    pub fn on_error<F>(&mut self, callback: F)
    where
        F: Fn(&str, &str) + Send + Sync + 'static,
    {
        self.on_error.push(Box::new(callback));
    }

    /// Process pending file changes (call from main loop)
    pub fn process_changes(&mut self) -> Vec<ReloadResult> {
        let changes = self.watcher.poll();
        let mut results = Vec::new();

        for change in changes {
            if change.kind == ChangeKind::Deleted {
                // Handle deleted files if needed
                continue;
            }

            match self.reload_file(&change.path) {
                Ok(module_name) => {
                    results.push(ReloadResult::Success(module_name.clone()));
                    for callback in &self.on_reload {
                        callback(&module_name);
                    }
                }
                Err(e) => {
                    let path_str = change.path.display().to_string();
                    results.push(ReloadResult::Error(path_str.clone(), e.clone()));
                    for callback in &self.on_error {
                        callback(&path_str, &e);
                    }
                }
            }
        }

        results
    }

    /// Reload a single file
    fn reload_file(&mut self, source: &Path) -> Result<String, String> {
        // Determine output path
        let output = self.source_map
            .get(source)
            .cloned()
            .unwrap_or_else(|| source.with_extension("smf"));

        // Recompile
        self.compiler.compile(source, &output)
            .map_err(|e| format!("Compile error: {:?}", e))?;

        // Load new module
        let new_module = self.modules.reload(&output)
            .map_err(|e| format!("Load error: {:?}", e))?;

        let module_name = source.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        // Check for breaking changes
        self.check_breaking_changes(&new_module)?;

        // Patch symbols
        self.patch_symbols(&new_module)?;

        // Bump version
        self.versions.write().unwrap().bump_module(&module_name);

        Ok(module_name)
    }

    /// Check if reload would break running code
    fn check_breaking_changes(&self, module: &LoadedModule) -> Result<(), String> {
        let versions = self.versions.read().unwrap();

        // Check type layouts
        for (type_name, type_info) in module.type_info() {
            let new_hash = crate::version::calculate_layout_hash(&type_info);

            if versions.type_layout_changed(&type_name, new_hash) {
                // Check if migration function exists
                if !self.migrator.has_migration(&type_name) {
                    return Err(format!(
                        "Breaking change: type '{}' layout changed with no migration",
                        type_name
                    ));
                }
            }
        }

        Ok(())
    }

    /// Patch function pointers in trampoline table
    fn patch_symbols(&self, module: &LoadedModule) -> Result<(), String> {
        let mut table = TRAMPOLINES.write().unwrap();

        for (name, sym_type) in module.exports() {
            if sym_type == crate::smf::SymbolType::Function {
                if let Some(ptr) = module.get_function::<*const ()>(&name) {
                    table.update_by_name(&name, ptr);
                }
            }
        }

        Ok(())
    }

    /// Run reload loop (blocking)
    pub fn run_loop(&mut self) {
        loop {
            let change = self.watcher.wait();

            if change.kind == ChangeKind::Deleted {
                continue;
            }

            match self.reload_file(&change.path) {
                Ok(module_name) => {
                    println!("[reload] {} reloaded successfully", module_name);
                    for callback in &self.on_reload {
                        callback(&module_name);
                    }
                }
                Err(e) => {
                    eprintln!("[reload] Error: {}", e);
                    for callback in &self.on_error {
                        callback(&change.path.display().to_string(), &e);
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum ReloadResult {
    Success(String),
    Error(String, String),
}
```

---

## Symbol Patcher

### Patcher Implementation (patcher.rs)

```rust
// crates/hotreload/src/patcher.rs

use std::collections::HashMap;
use crate::trampoline::FnPtr;

/// Patches function pointers for hot reload
pub struct SymbolPatcher {
    /// Old function pointers for rollback
    old_pointers: HashMap<String, FnPtr>,
    /// Patch history for debugging
    history: Vec<PatchRecord>,
}

#[derive(Debug)]
struct PatchRecord {
    symbol: String,
    old_ptr: usize,
    new_ptr: usize,
    timestamp: std::time::Instant,
}

impl SymbolPatcher {
    pub fn new() -> Self {
        Self {
            old_pointers: HashMap::new(),
            history: Vec::new(),
        }
    }

    /// Patch a symbol with new pointer
    pub fn patch(&mut self, name: &str, old_ptr: FnPtr, new_ptr: FnPtr) {
        // Save old pointer for potential rollback
        self.old_pointers.insert(name.to_string(), old_ptr);

        // Record patch
        self.history.push(PatchRecord {
            symbol: name.to_string(),
            old_ptr: old_ptr as usize,
            new_ptr: new_ptr as usize,
            timestamp: std::time::Instant::now(),
        });
    }

    /// Rollback to previous version
    pub fn rollback(&self, name: &str) -> Option<FnPtr> {
        self.old_pointers.get(name).copied()
    }

    /// Clear old pointers (after GC confirms old code is unreachable)
    pub fn clear_old(&mut self) {
        self.old_pointers.clear();
    }

    /// Get patch history for debugging
    pub fn history(&self) -> &[PatchRecord] {
        &self.history
    }
}
```

---

## State Migration

### Migrator Implementation (migration.rs)

```rust
// crates/hotreload/src/migration.rs

use std::collections::HashMap;
use std::any::Any;

/// Handles state migration during type changes
pub struct StateMigrator {
    /// Migration functions: type_name -> migration_fn
    migrations: HashMap<String, MigrationFn>,
}

type MigrationFn = Box<dyn Fn(&dyn Any) -> Box<dyn Any> + Send + Sync>;

impl StateMigrator {
    pub fn new() -> Self {
        Self {
            migrations: HashMap::new(),
        }
    }

    /// Register a migration function for a type
    pub fn register<T, U>(&mut self, type_name: &str, migrate: fn(&T) -> U)
    where
        T: 'static,
        U: 'static,
    {
        let migration = move |old: &dyn Any| -> Box<dyn Any> {
            let old_typed = old.downcast_ref::<T>()
                .expect("Type mismatch in migration");
            Box::new(migrate(old_typed))
        };

        self.migrations.insert(
            type_name.to_string(),
            Box::new(migration),
        );
    }

    /// Check if migration exists for type
    pub fn has_migration(&self, type_name: &str) -> bool {
        self.migrations.contains_key(type_name)
    }

    /// Migrate a value
    pub fn migrate(&self, type_name: &str, value: &dyn Any) -> Option<Box<dyn Any>> {
        self.migrations.get(type_name).map(|f| f(value))
    }
}

/// Example migration usage:
/// ```simple
/// # Old version
/// struct Player:
///     name: str
///     health: i64
///
/// # New version
/// struct Player:
///     name: str
///     health: i64
///     max_health: i64    # New field
///
/// # Migration function (generated or manual)
/// fn migrate_Player_v1_to_v2(old: &PlayerV1) -> PlayerV2:
///     return PlayerV2(
///         name: old.name,
///         health: old.health,
///         max_health: 100,  # Default value for new field
///     )
/// ```
```

---

## Compiler Integration

### Reloadable Code Generation

The compiler needs to generate code that uses trampolines for reloadable functions:

```rust
// In codegen/cranelift.rs - modifications for hot reload support

impl CraneliftCodegen {
    /// Generate call through trampoline table
    fn generate_reloadable_call(
        &mut self,
        builder: &mut FunctionBuilder,
        func_name: &str,
        args: &[Value],
    ) -> Value {
        // 1. Load trampoline table base address
        let table_addr = self.get_trampoline_table_addr(builder);

        // 2. Calculate function slot offset
        let func_id = self.get_function_id(func_name);
        let slot_offset = builder.ins().iconst(types::I64, (func_id * 8) as i64);

        // 3. Load function pointer from table
        let slot_addr = builder.ins().iadd(table_addr, slot_offset);
        let func_ptr = builder.ins().load(
            types::I64,
            MemFlags::new(),
            slot_addr,
            0,
        );

        // 4. Call indirect through pointer
        let sig = self.get_function_signature(func_name);
        let sig_ref = builder.import_signature(sig);
        let call = builder.ins().call_indirect(sig_ref, func_ptr, args);

        builder.inst_results(call)[0]
    }
}
```

---

## Usage Example

```rust
use simple_hotreload::{ReloadManager, TRAMPOLINES};
use simple_loader::ModuleRegistry;
use std::sync::Arc;
use std::path::Path;

fn main() {
    // Setup module registry
    let modules = Arc::new(ModuleRegistry::new());

    // Create reload manager
    let mut manager = ReloadManager::new(modules.clone()).unwrap();

    // Watch source directory
    manager.watch(Path::new("./src")).unwrap();

    // Map source files to outputs
    manager.map_source(
        Path::new("./src/game.simple").to_path_buf(),
        Path::new("./build/game.smf").to_path_buf(),
    );

    // Register callbacks
    manager.on_reload(|module| {
        println!("Module '{}' reloaded!", module);
    });

    manager.on_error(|file, error| {
        eprintln!("Failed to reload '{}': {}", file, error);
    });

    // Initial load
    modules.load(Path::new("./build/game.smf")).unwrap();

    // Game loop
    loop {
        // Process any pending reloads
        manager.process_changes();

        // Call reloadable function through trampoline
        unsafe {
            let update: fn(f32) = std::mem::transmute(
                TRAMPOLINES.read().unwrap().get_by_name("game_update").unwrap()
            );
            update(0.016);  // 60fps delta
        }

        // ... rest of game loop
    }
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-hotreload"
version = "0.1.0"
edition = "2021"

[dependencies]
notify = "6.1"
lazy_static = "1.4"

simple-compiler = { path = "../compiler" }
simple-loader = { path = "../loader" }
```

---

## Summary

| Component | Purpose |
|-----------|---------|
| `trampoline.rs` | Indirect function calls for atomic updates |
| `watcher.rs` | File system monitoring |
| `version.rs` | Track module/type versions |
| `manager.rs` | Coordinate reload process |
| `patcher.rs` | Update symbol pointers |
| `migration.rs` | Handle breaking type changes |

Hot reload flow:
1. File watcher detects change
2. Compiler recompiles modified source
3. Loader loads new module
4. Version tracker checks for breaking changes
5. Trampoline table updated atomically
6. Old code garbage collected when unreferenced
