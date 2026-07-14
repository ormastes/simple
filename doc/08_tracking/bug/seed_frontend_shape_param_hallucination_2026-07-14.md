# Seed frontend regression: spurious "expects argument for parameter 'shape'" blocks all native-builds

**Introduced by** a parallel mid-flight change committed in the current Rust
source (around `b1efbf95bfe` "wip: working-copy snapshot (session sync)"). Any
seed built from current-origin `src/compiler_rust` fails to `native-build` even a
trivial program.

## Symptom

A freshly-built seed (`cargo build --profile bootstrap -p simple-driver` from
current origin) fails on EVERY `native-build` with:

```
error: semantic: function expects argument for parameter 'shape', but none was provided
  --> src/compiler/50.mir/mir_data.spl:64  (the MirFunction(...) constructor)
  --> src/compiler/60.mir_opt/mir_opt/mod.spl:363-365
```

## It is a FRONTEND HALLUCINATION, not a real missing field

- There is **no `shape` field** in `MirFunction` (mir_instructions.spl:588),
  `MirSignature` (mir_types.spl:50), or any MIR struct — grep for `^\s+shape:`
  in `src/compiler/50.mir/*.spl` is empty.
- The **old** bootstrap seed (`src/compiler_rust/target/bootstrap/simple`,
  Jul-13) compiles the SAME current `.spl` source cleanly (e.g. a trivial enum
  program builds and runs `a=16`). So the `.spl` source is correct.
- Therefore the defect is in the **Rust frontend** (semantic analysis) as of the
  current committed source — it fabricates a `shape` parameter requirement.

## Impact (critical for the redeploy)

Every seed built from current origin cannot native-build anything → the staged
redeploy cannot produce a working compiled pure-Simple compiler from this source
state, and independent verification of backend fixes (e.g. the box_int DEFECT B
fix `38809ec11790`) is blocked: the old seed has the pre-fix backend, and a new
seed built with the fix inherits this frontend regression.

## Fix

Bisect the Rust frontend commits since the last good seed (Jul-13) to find the
change that injected a spurious `shape` parameter into constructor/call semantic
checking (likely near tensor/VHDL/shape-typed handling that leaked into general
struct-constructor arg validation). Restore correct behavior: a struct
constructor must only require its declared fields.

## Verification handle

`<fresh seed> native-build --entry <trivial enum program>` must succeed (old seed
does). Evidence: build log in session scratchpad `seed_build.log` (SEED_BUILD_RC=0
but every subsequent native-build errors on 'shape').
