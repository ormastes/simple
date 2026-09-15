# The native object cache misses an identical second build it has a valid entry for

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-6, `work/bootstrap-full-4-2026-09-12`
- Severity: performance and, until BOOT-6's publish fix, the trigger for a hard
  build failure — a miss makes the driver recompile, and the recompile then
  collided with the object the first build had published.

## Measured

Two positional `native-build`s of
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` sharing one `HOME`,
Stage-2 candidate `67786227817bf45f...`. After the first build the scope
directory holds everything a hit needs:

```
.../native-build/v1/build_cache.sdn                       (entry present, outputs named)
.../native-build/v1/se3b0c44298fc1c149afbf4c8996fb924/
    object.scripts.check.cert.redeploy_gate.fixtures.hello_world.o                  1080 bytes
    object.scripts.check.cert.redeploy_gate.fixtures.hello_world.o.capsule-receipt  1565 bytes
    native-module-witness-shadow-v1.receipt
```

The second build nonetheless reports `cached=0` in its `native_cache` progress
line and recompiles. `SIMPLE_COMPILER_TRACE=1` prints no `[NATIVE] cache hit`
line and no line naming which sub-condition declined, so the reason is
UNMEASURED. A third build behaves identically, so this is deterministic, not a
warm-up artifact.

## Where to look

`src/compiler/80.driver/driver_aot_native_output.spl:1812-1855`. The hit needs,
in order: `source_snapshot_matches and witness_reason == "match"` (else
`cached_outputs` is nil and the whole block is skipped), then `all_in_scope`,
`scoped_outputs.len() == 1`, `outputs_exist`, and
`driver_native_capsule_result_valid_v1(cached_capsule)`.

Note the asymmetry that made this dangerous: the invalidation branch
(`build_cache.remove_entry(cache_source)`) sits INSIDE `if cached_outputs.?:`.
When the miss happens before that — which is what happens here — nothing
invalidates and nothing removes the stale published object either. The driver
therefore never sees the object it is about to collide with; only the backend's
publish site does, which is where BOOT-6 put the fix.

## Not fixed

BOOT-6 fixed the collision (`llvm_backend_tools.spl` now clears a stale
destination before publishing), not the miss. After that fix the second build
succeeds by RECOMPILING; `cached=0` remains. Diagnosing the miss needs a trace
line naming the declining sub-condition, which does not exist today.
