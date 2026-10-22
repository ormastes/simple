# Windows stage-2 bootstrap link fails without MSVC env; cache identity pins env (2026-10-22)

## Symptom

On Windows (`x86_64-pc-windows-msvc`), the stage-2 native build compiles all
modules then fails at link time:

```
Build failed: link failed: lld-link: error: could not open 'kernel32.lib': no such file or directory
```

A separate retry then fails earlier with:

```
bootstrap-cache-error: incompatible producer/options/runtime/tool ABI/source identity: .../stage2-native-cache; specify --invalidate-cache=stage2
```

## Root cause

1. `bootstrap-from-scratch.sh` captures `LIB`/`INCLUDE`/`LIBPATH` from the
   ambient environment (`bootstrap_windows_lib_env="LIB=${LIB:-}"`,
   ~line 2540) and forwards them to the sandboxed stage-2/3 link steps. On a
   plain Git Bash shell these are UNSET, so `lld-link` receives an empty `LIB`
   and cannot resolve `kernel32.lib` even though the Windows SDK is installed.
2. The stage-2 cache binding (`bootstrap_cache_context_payload stage2`) folds
   the Windows include/lib environment into the cache identity hash. A cache
   built without the MSVC env can never be reused once the env is provided,
   and vice versa — the cache legitimately rejects it (`old cache preserved`).

## Fix (operator environment, no repo change)

Source the repo's own env scripts before invoking the bootstrap:

```bash
. scripts/setup/windows-msvc-bootstrap-env.shs   # vswhere-discovered INCLUDE/LIB/LIBPATH
. /c/Users/user/.simple/toolchains/activation/windows-llvm-23.1.1.shs  # pinned LLVM 23.1.1
export LLVM_HOME='C:/Users/user/.simple/toolchains/llvm-msvc-23.1.1/clang+llvm-23.1.1-x86_64-pc-windows-msvc'
export SIMPLE_NATIVE_FILE_TIMEOUT=1200           # 5 default-timed-out files need >300s
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
   --keep-going --invalidate-cache=stage2        # required once when the env changes
```

Notes:
- `windows-msvc-bootstrap-env.shs` ends `return 1` on this host because its
  LLVM tail expects a `/c/dev/tool/...` layout; the MSVC exports (line 225
  `export INCLUDE LIB`) happen BEFORE that and are what the bootstrap needs.
- The default 300 s per-file timeout is insufficient for
  `src/app/io/mod.spl`, `10.frontend/core/interpreter/__init__.spl`,
  `parser_expr.spl`, `20.hir/generated/hir_codec.spl`, and
  `70.backend/backend/native/mach_inst.spl` under the Rust seed
  (5 timeouts observed; all five compiled with 1200 s).
- A previous attempt's `stage2-runtime-authority` directory must be sealed
  before the next run archives it:
  `powershell ... phase2-capsule-permissions.ps1 -Action freeze -Path <dir>`.

## Evidence

- 2026-10-22 on `release_phase3`: stage-2 link failed with kernel32.lib in
  three consecutive runs until the MSVC env script was sourced; the next run
  then failed the cache binding with the "incompatible
  producer/options/runtime/tool ABI/source identity" message above (proving
  the env is part of the cache identity). With `--invalidate-cache=stage2`
  and the full env, the run reached `compiled=7 reused=1092 failed=0` on a
  warm cache before the remaining link/env-chain issues were resolved. The
  full clean-identity rebuild result is recorded in
  `.build/full-bootstrap-20261021.log` and the stage-2 verification summary.
