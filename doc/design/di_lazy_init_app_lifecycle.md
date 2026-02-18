# Dependency Injection, Lazy Init, and App Lifecycle Design

**Date:** 2026-02-18
**Status:** Research / Proposal

---

## 1. App Lifecycle: `init()`, `reset()`, `main()`

### Current State

Simple has no formal lifecycle hooks. Entry points are ad-hoc:
- CLI entry: `cli_main()` in `src/app/cli/main.spl`
- No global `init()` / `reset()` convention
- Module-level top-level expressions run at first `use` (implicit init)

### Proposed Convention

Adopt an explicit naming convention (not new syntax, just rules):

```simple
# main.spl — program entry point
fn main():
    init()          # wire the DI container
    run_app()       # do the work

fn init():
    # Register all services into the DI container (lazy)
    # Called once at startup
    pass_do_nothing

fn reset():
    # Tear down and rebuild state — used in tests only
    # Clears caches, resets singletons
    pass_do_nothing
```

**Rules:**

| Function | When to use | Called by |
|----------|-------------|-----------|
| `main()` | Program entry; call `init()` then start work | Runtime or test harness |
| `init()` | Wire DI; register lazy services | `main()` or test setup |
| `reset()` | Destroy and re-init state | Test `before_each` / `after_each` hooks |

**Key principle:** `init()` only *registers* things — it does not *create* them. Creation happens lazily on first use.

---

## 2. Current DI Pattern (Status Quo)

Simple currently uses **manual composition** — no DI container:

```simple
# Config struct per component
struct DatabaseConfig:
    url: text
    pool_size: i64

fn databaseconfig_default() -> DatabaseConfig:
    DatabaseConfig(url: "sqlite://local.db", pool_size: 5)

# Factory function creates component with injected config
fn database_new(config: DatabaseConfig) -> Database:
    Database(url: config.url, pool: ConnectionPool(config.pool_size))

# Wire manually in main
fn main():
    val db_config = DatabaseConfig(url: env_var("DB_URL"), pool_size: 10)
    val db = Database__new(db_config)
    val svc = UserService(db: db)
    run(svc)
```

**Strengths:** Explicit, no magic, easy to trace.
**Weaknesses:** Wiring is in `main()` — grows unwieldy; no lazy init; hard to override in tests.

---

## 3. Proposed: `lazy val` — Language-Level Lazy Initialization

### Syntax

```simple
lazy val database = Database(url: config.db_url)
lazy val logger = ConsoleLogger(level: "info")
lazy val user_service = UserService(db: database, log: logger)
```

**Semantics:**
- `lazy val x = expr` — `expr` is evaluated the **first time `x` is accessed**
- Subsequent accesses return the cached value
- Dependencies between `lazy val`s are resolved by access order (DAG guaranteed by constructor params)

### Interpreter Implementation

The interpreter needs a **lazy cell** — a wrapper that holds either an unevaluated thunk or a computed value:

```
State: Uninitialized(closure: () -> T)
     | Initialized(value: T)
```

On attribute/name access:
1. Check state.
2. If `Uninitialized`: run closure, store result, transition to `Initialized`.
3. If `Initialized`: return cached value.

This is identical to **Python's `importlib.util.LazyLoader`** approach: a stub object exists in the symbol table from declaration time, but execution is deferred.

### Python and JS Comparison

| Language | Mechanism | How deferred? |
|----------|-----------|---------------|
| Python | `LazyLoader` | Module object in `sys.modules` immediately; `__getattr__` triggers real load |
| JS (Node.js) | `require()` + `require.cache` | First `require()` executes file, caches; subsequent calls return cache |
| JS (bundler) | `import()` dynamic | Returns a Promise; bundler code-splits into separate chunk |
| Kotlin | `lazy {}` delegate | Wrapper object with `volatile` flag; double-checked locking |
| C++11 | Magic statics | Compiler inserts `__cxa_guard`; thread-safe one-time init |
| Go | `sync.Once` | Atomic flag fast path; mutex slow path |
| Scala | `lazy val` | 2-bit state bitmap (`Uninitialized` / `Initializing` / `Concurrent` / `Done`) + CAS |
| Swift | `static let` | Thread-safe (uses `dispatch_once` equivalent); instance `lazy var` is NOT thread-safe |

**For Simple (single-threaded interpreter):** No locking needed. Simple flag + closure is enough.

### Compiler-Level (AOT) Implementation

At compile time, `lazy val x = expr` desugars to:

```simple
# Compiler generates this internally:
var __x_initialized = false
var __x_value: T = nil   # placeholder

fn __x_get() -> T:
    if not __x_initialized:
        __x_value = expr
        __x_initialized = true
    __x_value

# All references to `x` become `__x_get()`
```

This is the Meyers Singleton pattern — identical to C++11 magic statics, minus threading.

---

## 4. DI via Module-Level `lazy val`

### Pattern: Service Registry Module

Create a `services.spl` module that declares all application services as `lazy val`:

```simple
# src/app/services.spl

use app.config
use app.database
use app.logging

lazy val app_config = load_config()           # reads config file
lazy val logger = ConsoleLogger(              # created when first used
    level: app_config.log_level
)
lazy val db = Database__new(DatabaseConfig(   # depends on app_config
    url: app_config.db_url,
    pool_size: app_config.db_pool_size
))
lazy val user_repo = UserRepository(db: db)   # depends on db
lazy val user_service = UserService(          # depends on user_repo + logger
    repo: user_repo,
    log: logger
)
```

### Wiring in `init()`

```simple
# src/app/main.spl
use app.services

fn main():
    init()
    val svc = services.user_service   # triggers lazy chain: config → db → repo → service
    run_server(svc)

fn init():
    # No work here — all services are lazy, wired by services.spl
    # Override for testing: substitute mock values before access
    pass_do_nothing
```

### Test Override Pattern

```simple
# test/app/user_service_spec.spl
use app.services

before_each:
    # Override lazy vals before any test accesses them
    services.db = MockDatabase()        # inject mock before lazy init fires
    services.logger = SilentLogger()

after_each:
    services.reset()   # clear all lazy vals back to uninitialized
```

**Key insight:** Because `lazy val` stores a flag, `reset()` just sets all flags back to `false`. This mirrors the Kotlin `LazyThreadSafetyMode.NONE` pattern, reset for test isolation.

---

## 5. Package Lazy Import

### Problem

`use app.database` loads and executes the module immediately. For large module trees, startup time grows linearly with imported module count — even if most modules are unused for a given command.

**Python solution:** `importlib.util.LazyLoader` — defers module execution until first attribute access.
**JS solution:** Dynamic `import()` — Promise-based, resolved lazily.

### Proposed Syntax

```simple
use lazy app.database    # Deferred: not loaded until a symbol from app.database is accessed
use app.logging          # Eager: loaded immediately (current behavior)
```

### Interpreter Implementation

The interpreter maintains two tables:

| Table | Contents |
|-------|----------|
| `loaded_modules` | Fully executed modules (current behavior) |
| `deferred_modules` | `{path → file_path}` — registered but not yet executed |

**On `use lazy app.database`:**
1. Resolve the file path (same as eager).
2. Add to `deferred_modules` table. Do NOT execute.
3. Add a **proxy namespace** for `app.database` in the symbol table — an object that knows its module path but has no symbols yet.

**On first symbol access from `app.database`:**
1. Name lookup reaches the proxy namespace.
2. Proxy triggers actual module load (execute file, populate symbols).
3. Proxy is replaced with the real module namespace.
4. Symbol lookup continues normally.

This is **identical to Python's `LazyLoader.__getattr__` trigger** mechanism.

### Module Manifest Optimization

To make lazy import work without executing the module, the interpreter needs to know *which symbols a module exports* without running it. Options:

1. **No manifest (simple approach):** On first access, execute the whole module. This is what Python's `LazyLoader` does — it just defers execution, not parsing.

2. **Module index (.smf header):** The SMF format already contains an export table. The interpreter can read just the header to know what symbols are available, then execute the body on first use.

Option 1 is correct for the interpreter. Option 2 enables richer tooling (IDE autocomplete without loading).

### Dependency Ordering with Lazy Imports

Circular `use lazy` is safe — unlike eager `use` which can deadlock:

```simple
# a.spl
use lazy b        # deferred

lazy val x = b.y  # b.y accessed here → b is loaded now

# b.spl
use lazy a        # deferred (a might be already loaded at this point)

lazy val y = 42   # no circular dependency actually triggered
```

The DAG is enforced by access order, not declaration order.

---

## 6. Interpreter: How Python and JS Solve Lazy Loading

### Python (PEP 302 / 451)

```python
import sys
import importlib.util

def install_lazy_loader():
    # Replace the default finder with one that wraps all loaders in LazyLoader
    old_path_hooks = sys.path_hooks[:]
    # ... wrap each hook's loader with LazyLoader
```

Python's trick:
1. `sys.modules[name]` is populated with a **stub module object** immediately.
2. The stub's `__class__` is replaced with a `_LazyModule` subclass that overrides `__getattr__`.
3. First attribute access calls `__getattr__` → runs the real loader → replaces `__class__` back to normal.

**Key limitation:** Only works for `import mod; mod.attr`. Does NOT work for `from mod import attr` (requires full load immediately).

### JavaScript / Node.js

Node.js CommonJS:
```javascript
// require.cache stores {filename: Module} after first load
// Subsequent require() returns cached Module.exports directly
const db = require('./database');  // first call: execute, cache
const db2 = require('./database'); // subsequent: return cache
```

Dynamic import (ESM):
```javascript
// Lazy load — returns Promise
async function getDatabase() {
    const { Database } = await import('./database.js');
    return new Database();
}
```

**Key insight for Simple:** Node.js `require.cache` is conceptually the same as `loaded_module_set` in Simple's interpreter. Dynamic `import()` is analogous to `use lazy`. Simple's single-threaded model makes it simpler — no Promise needed, just deferred execution.

---

## 7. Implementation Roadmap

### Phase 1: Convention (no new syntax)

- [ ] Document `init()` / `reset()` / `main()` naming convention
- [ ] Create `services.spl` pattern for existing apps
- [ ] Add `reset()` support to test hooks (`before_each` / `after_each`)

### Phase 2: `lazy val` keyword

- [ ] Parser: recognize `lazy val x = expr`
- [ ] Interpreter: implement lazy cell (flag + thunk)
- [ ] Compiler/AOT: desugar to `__x_initialized` + `__x_get()` pattern
- [ ] Test: verify single evaluation, value caching, DI chain ordering

### Phase 3: `use lazy` import

- [ ] Parser: recognize `use lazy mod.path`
- [ ] Interpreter: add `deferred_modules` table + proxy namespace
- [ ] Symbol lookup: trigger load on first proxy attribute access
- [ ] Test: verify deferred execution, correct ordering, reset behavior

### Phase 4: Module Manifest Index

- [ ] SMF header export table: readable without executing module body
- [ ] IDE/LSP: use manifest for autocomplete without full load
- [ ] Lazy import: use manifest to validate symbol names at parse time

---

## 8. Summary Table

| Feature | Status | Approach |
|---------|--------|----------|
| `init()` / `reset()` / `main()` | Convention only | Naming rules, no new syntax |
| DI via manual composition | Existing | Config structs + factory functions |
| DI via module-level `lazy val` | **Proposed** | Services module pattern |
| `lazy val` keyword | **Proposed** | Flag + thunk; desugar at compile time |
| `use lazy` import | **Proposed** | Proxy namespace + deferred execution |
| Module manifest | Future | SMF header index for tooling |

---

## References

- [PEP 302 - New Import Hooks](https://peps.python.org/pep-0302/)
- [PEP 690 - Lazy Imports](https://peps.python.org/pep-0690/)
- [Kotlin lazy delegate](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/lazy.html)
- [Dart get_it service locator](https://pub.dev/packages/get_it)
- [C++11 Magic Statics (thread-safe)](https://www.nuonsoft.com/blog/2017/08/10/implementing-a-thread-safe-singleton-with-c11-using-magic-statics/)
- [Go sync.Once](https://pkg.go.dev/sync#Once)
- [Scala SIP-20 Lazy Val bitmap](https://docs.scala-lang.org/scala3/reference/changed-features/lazy-vals-init.html)
- [Swift static properties (thread-safe)](https://www.jessesquires.com/blog/2020/07/16/swift-globals-and-static-members-are-atomic-and-lazily-computed/)
- [Webpack Code Splitting](https://webpack.js.org/guides/code-splitting/)
