# Circular `export use` reports "unknown static method" instead of an import cycle

- **Filed:** 2026-09-05
- **Lane:** `src/compiler_rust/target/debug/simple` (debug Rust seed, built from current source)
- **Severity:** diagnostic quality — misdirects the reader to the wrong file

## Symptom

Adding `export use std.driver.static_table.{register_static_driver}` to
`src/lib/nogc_sync_mut/driver/registry.spl` (which `static_table.spl` itself
imports) makes every spec that loads `std.driver.registry` die with:

```
[INFO] JIT compilation failed, falling back to interpreter: semantic: unknown static method empty on class DriverRegistry
error: semantic: unknown static method empty on class DriverRegistry
```

`DriverRegistry.empty()` is declared, correctly, at
`src/lib/nogc_sync_mut/driver/registry.spl:47` inside `impl DriverRegistry:`.
Nothing is wrong with that declaration, and the error names neither of the two
modules that form the cycle.

## Why this is a defect and not just a user error

The cycle is the user's error. The *message* is the defect: it points at a
declaration that is present and valid, in a file the reader has no reason to
suspect, and says the method does not exist. The real condition is that
`static_table.spl`'s module-global initializer

```
var __STATIC_REGISTRY: DriverRegistry = DriverRegistry.empty()   # static_table.spl:35
```

runs while `registry.spl` is still mid-load (it is waiting on `static_table`
via the `export use`), so `impl DriverRegistry`'s static methods are not yet
registered. A cycle diagnostic naming both modules and the edge that closes
the loop would have made this a ten-second fix; as it stands it reads as a
broken `static fn`.

## Minimal reproducer

Two modules, A `export use`-ing B while B imports A, with a module-global in B
initialised by a static method declared in A.

Control (no cycle) — this passes, printing `0`, which is what makes the
message misleading:

```
# repro.spl
use std.driver.registry.{DriverRegistry}
var __R: DriverRegistry = DriverRegistry.empty()
fn main():
    print(__R.entries.len())
```

```
$ src/compiler_rust/target/debug/simple run repro.spl
0
```

Then add `export use std.driver.static_table.{register_static_driver}` to
`registry.spl:12` and re-run any spec importing `std.driver.registry` to see
the error above.

## Expected

An import-cycle diagnostic naming the participating modules and the edge that
closes the cycle, e.g.
`import cycle: std.driver.registry -> std.driver.static_table -> std.driver.registry`.

## Impact on the plan-acceptance lane

`test/03_system/plan_acceptance/driver_framework_module_level_sugar_spec.spl`
imports `register_static_driver` from `std.driver.registry`, but the function
is defined in `std.driver.static_table` and cannot be re-exported from
`registry.spl` without forming this cycle. That scenario
(REQ-PLAN-DRIVER-SUGAR-008) therefore fails honestly with
`function register_static_driver not found` and its plan checkbox stays open.
Closing it needs the function's owning module resolved (move the static
registry state, or introduce a third module both can import), not a
re-export.
