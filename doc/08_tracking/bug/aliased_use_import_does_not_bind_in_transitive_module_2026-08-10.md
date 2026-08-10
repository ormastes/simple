# Aliased `use ... { x as y }` does not bind when the module is reached transitively

**Status:** OPEN — compiler defect. Worked around at one call site; the defect itself is unfixed.
**Filed:** 2026-08-10
**Found by:** diagnosing `wm_action_applier_spec` `reason=zero-examples`
(`doc/08_tracking/bug/wm_action_applier_spec_dead_on_both_legs_vulkan_order_env_get_2026-08-10.md`).

## Symptom

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:10` declared

```
use std.gc_async_mut.io.mod_stub.{env_get as vulkan_order_env_get}
```

and used the alias at module scope. Any spec whose import closure reaches this
file transitively (e.g. via `os.compositor.compositor`) failed with

```
error[E1002]: function `vulkan_order_env_get` not found
error: test-runner: no examples executed
```

which the harness reports as `executed=0 ... reason=zero-examples` — the spec is
dead, never runs, and can never fail on its own content.

## Isolation (what is and is not the cause)

Three hypotheses were tested and **falsified**, so record them so nobody retries:

| Hypothesis | Probe | Result |
|---|---|---|
| Alias through an `export use` re-export barrel is unsupported | changed the import to the defining module `std.gc_async_mut.io.env_ops` | still E1002 — **not the cause** |
| Aliased imports are broken under the `test` engine | 1-example spec aliasing `env_get`, run under `bin/simple test` | `1 total, 1 passed` — **not the cause** |
| Aliases are invisible to module-level `val` initializers | spec with `val _P = probe2_env_get(...)` at module scope | `1 total, 1 passed` — **not the cause** |

The surviving discriminator is **entry-file vs transitive**: the identical alias
resolves when the declaring file is the entry module, and fails to bind when the
file is pulled in as a transitive dependency. Sibling
`backend_vulkan_glsl.spl:27` uses the same aliasing form and does not surface —
it is simply not in the same closures yet, so it is a latent instance of the
same defect, not a counter-example.

## Impact

Silent and severe. The alias failure reaches codegen as a missing *function*,
which aborts the whole compilation unit; for a spec this turns into
`zero-examples`, i.e. a file that sits in the corpus claiming `@cover` while
asserting nothing. Every `use ... { x as y }` in a library module is a candidate.

## Current state

`backend_vulkan_helpers.spl` no longer aliases: it declares
`extern fn rt_env_get(key: text) -> text` directly (`env_ops.env_get` is a
one-line forwarder to that same extern, so behaviour is identical) and the
`val _VULKAN_ORDER_TRACE_ENABLED` probe gate is unchanged. That unblocked the
spec but does **not** fix the compiler.

## Unblock condition

Aliased imports must bind identically whether the declaring module is the entry
file or a transitive dependency. Add a regression spec that imports an aliasing
library module transitively and asserts the aliased call resolves.

## Do not

Do not close this by converting the remaining aliased imports to plain imports.
That hides the defect; the alias form is valid grammar and must work.
