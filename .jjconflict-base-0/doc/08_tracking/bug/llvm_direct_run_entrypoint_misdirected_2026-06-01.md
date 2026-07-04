# llvm_direct run entrypoint misdirected

Status: open (triaged 2026-06-11)

Date: 2026-06-01

## Summary

`simple run src/app/compile/llvm_direct.spl ...` does not currently execute the
`llvm_direct.spl` CLI entrypoint. During the profile-guided executable
optimization audit it exited `0` after running `src/compiler/00.common/effects_solver.spl`
tests and produced neither the requested output binary nor the
`<output>.simple-profile-counters` sidecar.

## Reproduction

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple run \
  src/app/compile/llvm_direct.spl \
  test/01_unit/compiler/backend/_codegen_smoke.spl \
  /tmp/simple_pgo_smoke \
  --simple-profile-counters --verbose
```

Observed stdout:

```text
Fixed-Point Solver Tests
========================
All fixed-point solver tests passed!
```

Observed filesystem:

```text
/tmp/simple_pgo_smoke: missing
/tmp/simple_pgo_smoke.simple-profile-counters: missing
```

## Impact

This blocks command-level proof that `--simple-profile-counters` reaches native
compile output and writes durable sidecar metadata, even though the
instrumentation helpers and sidecar path are covered by focused system specs.

## Notes

The first attempt also exposed stale `EffectTag.Sync`/`EffectTag.Async`
references in `src/compiler/00.common/effects_solver.spl`; those were corrected
to `EffectTag.PureTag`/`EffectTag.SuspendingTag`.

## Update: 2026-06-01 10:08 UTC

The current worktree no longer stops at the imported effect self-test entrypoint:

- `src/compiler/00.common/effects.spl` renamed its library self-test from
  `main` to `effects_selftest_main`.
- `src/compiler/00.common/effects_solver.spl` renamed its library self-test from
  `main` to `effects_solver_selftest_main`.

After that fix, both the original `_codegen_smoke.spl` fixture and a minimal
`fn main() -> i64: return 0` fixture still fail command-level proof. The
interpreter reaches compiler module loading and then aborts:

```text
thread 'simple-main' has overflowed its stack
fatal runtime error: stack overflow, aborting
exit=134
binary=missing
metadata=missing
```

Impact remains the same for the profile-guided executable optimization slice:
helper-level and SPipe evidence proves durable sidecar metadata generation, but
command-level `llvm_direct.spl --simple-profile-counters` evidence is still
blocked by this compiler/interpreter stack overflow.

## Update: 2026-06-01 10:18 UTC

`src/app/compile/llvm_direct.spl` no longer imports `app.compile.native` only to
reach the unused `find_cpp_compiler` helper. That removes the hard stack
overflow in the minimal smoke, but exposes the next command-path blocker:

- `compiler.driver.driver` does not export `aot_c_file` at runtime.
- `compiler.driver.driver_api_codegen_backends.aot_c_file` cannot resolve the
  lazy `compiler_driver_create` symbol in this script execution mode.
- `compiler.driver.driver_api.aot_c_file` delegates to
  `simple compile --backend=c -o <path>`, but the Rust compile command currently
  treats non-native `--backend=c` as an SMF compile and writes SMF bytes instead
  of C/C++ source.
- `simple compile --native --backend=c` rejects `c` as an unsupported native
  backend.

Current minimal reproduction:

```bash
printf 'fn main() -> i64:\n    return 0\n' > /tmp/simple_pgo_min.spl
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple \
  src/app/compile/llvm_direct.spl \
  /tmp/simple_pgo_min.spl /tmp/simple_pgo_min \
  --simple-profile-counters --verbose --clean
```

Observed:

```text
exit=1
binary=missing
metadata=missing
```

Root cause is now narrowed to C-backend entrypoint availability for
`llvm_direct`: the profile-counter command needs a real C/C++ emission route
before it can compile, write `<output>.simple-profile-counters`, and complete
the end-to-end smoke.

## Resolution: 2026-06-01 10:32 UTC

The command-level profile-counter smoke now passes in the bootstrap driver:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple \
  src/app/compile/llvm_direct.spl \
  test/01_unit/compiler/backend/_codegen_smoke.spl \
  /tmp/simple_pgo_smoke \
  --simple-profile-counters --verbose --clean
```

Observed:

```text
exit=0
binary=present size=16176
run_exit=0
metadata=present lines=6
records=4
```

The sidecar contains function-entry metadata for `make_text`, `make_obj`,
`make_gpu`, and `main`, and the native binary contains
`__simple_profile_counters` symbols. The metadata was also converted to a
reloadable `.sprof` file and consumed by `src/app/optimize/main.spl
--layout-plan` to write a deterministic hot/cold layout manifest.

Resolution changes:
- imported compiler-library self-test entrypoints were renamed away from
  `main`;
- `llvm_direct.spl` uses the standard CLI arg helper and accepts direct
  `simple run <file> <source> <output> ...` arguments;
- `llvm_direct.spl` reaches real C emission through
  `compiler.driver.driver_api.aot_c_file`;
- `src/compiler/70.backend/__init__.spl` no longer exports the missing
  `compiler.backend.wffi_bindgen` module, so `compiler.backend` loads in the
  command path.
