# Calling an undefined method on a struct is deferred to the LINKER, not reported as a semantic error

**Filed:** 2026-09-12
**Found by:** sanctioned bootstrap (`--full-bootstrap --stop-after-stage2`) on aarch64, at 28a96c436b9
**Status:** OPEN (the two call sites it hid are fixed; the fail-open itself is NOT)

## Symptom

Stage 2 ran for ~102 minutes, compiled ~1,900 objects, and then died at link:

    Build failed: link failed: mold: error: undefined symbol: GenericTemplate.is_err
    clang++: error: linker command failed with exit code 1

## Why this is a fail-open, not just a bad error message

`GenericTemplate` (`src/compiler/00.common/compilation_context.spl:99`) is a `struct` with
**no `impl` block at all**, so `is_err` exists nowhere in the tree. The call site
(`src/compiler/40.mono/instantiation.spl:72`) called `.is_err()` on a value whose declared
type is `GenericTemplate?`.

A method that does not exist on the receiver's declared type is decidable at compile time.
Instead, codegen emitted an **unqualified** relocation `GenericTemplate.is_err` and let the
link fail. The asymmetry is visible in the object file: every symbol the module *defines* is
namespaced, only the bogus one is bare.

    $ nm --defined-only .../native-objects-xRB5OA/mod_325.o
    compiler__mono__instantiation__TemplateInstantiator.instantiate
    compiler__mono__instantiation__TemplateInstantiator.is_cached
    ... (all namespaced)
    $ nm -u .../mod_325.o | grep GenericTemplate
    GenericTemplate.is_err          <-- unqualified

## A second instance was hiding behind the first

mold stops at the first error, so only one was reported. Differencing undefined against
defined symbols over every object in the stage-2 object dir found a sibling of the same class:

    DynamicBackendPluginLease.admitted_handle

`DynamicBackendPluginLease` (`src/compiler/70.backend/backend_plugin/dynamic_loader.spl:79`)
defined `symbol_name` / `is_open` / `close` and no `admitted_handle`, yet
`dynamic_adapter.spl:104` and `:131` both call it. So the population of these is not
self-evidently 1; a ratchet should count them.

## Cost of the fail-open

Both defects are one-line-visible at their call sites. Because they are only caught by the
linker, each one costs a full Stage 2 (~100 min here) to surface, **one at a time**, since
mold reports the first and stops. That is the expensive part, not the fix.

## Suggested fix direction (not implemented)

Reject an unresolved method on a *known, non-dynamic* receiver type during semantic analysis.
Note the compiler already does this for builtins — a probe produced
`error: semantic: method 'len' not found on type 'i64'` — so the machinery exists; it is the
user-struct path that falls through to codegen.

Cheap interim guard: after stage-2 object generation, diff `nm -u` against `nm --defined-only`
plus the runtime archive and fail on any residual `Type.method`-shaped symbol. That is exactly
the check that found the second instance here, and it runs in seconds.

## Related

- `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` — same family: a missing
  binding that produces no diagnostic at the point of use.
- The struct/enum name collision on `GenericTemplate` (struct at `compilation_context.spl:99`,
  **enum** at `40.mono/monomorphize/deferred.spl:36`) is a separate, still-open smell.
