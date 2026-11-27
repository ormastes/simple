# Windows-gnu host rejects its own target in the hosted C plan (2026-10-24)

## Symptom
Stage2 (pure-Simple bootstrap CLI, windows-gnu lane) `native-build hello.spl
--target x86_64-pc-windows-gnu` compiles, then the link fails:
`host C runtime/entry compilation unsupported: target 'x86_64-pc-windows-gnu' on host 'x86_64-windows'`.

## Cause
`hosted_c_target_os_matches` (`src/compiler/70.backend/backend/runtime_compiler.spl`)
and `hosted_c_target_matches_host` (`llvm_native_link_hosted_support.spl`) accepted
only `-pc-windows-msvc` for a Windows host, so `hosted_c_compiler_plan` returned
`supported: false` for the native gnu target. The mingw link path downstream
(`_is_mingw`, `_link_mingw`) already existed and was unreachable. The
MinGW compiler discovery also preferred `gcc`; the gnu lane is llvm-mingw clang only.

This hits the sanctioned path: `bootstrap-from-scratch.sh` stage3 runs
`stage2 native-build --target "${PLATFORM}"` with `PLATFORM=x86_64-pc-windows-gnu`.

## Fix
Accept `-pc-windows-gnu` on a Windows host in both predicates; MinGW discovery
probes `clang` only. Spec: `test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl`.

## WA-WINGNU-ARCH-ONLY-TARGET (until a stage2 carrying the fix is deployed)
An arch-only target inherits the host OS and passes the gate. Verified with the
prebuilt stage2 (`simple-bootstrap 1.0.0-rc.1`), output `hello`, rc 0:

```sh
. build/run-new-env.sh            # gnu lane env (llvm-mingw clang first)
export CC="$(cygpath -m "$LLM/bin/clang.exe")"   # GNU link requires an absolute .../clang.exe in CC
export SIMPLE_PROJECT_ROOT=<repo root with src/runtime + tools/counterpart/sdk>
export SIMPLE_SCV_INVENTORY_COLD_INIT=1          # ad-hoc single file: no compile-event journal
stage2/simple.exe native-build hello.spl --target x86_64 -o hello.exe
./hello.exe                                       # -> hello
```

Remove the workaround once the deployed stage2 includes this fix.
