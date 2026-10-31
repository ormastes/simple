# Stage 2 AOT fails "llc failed (exit -1)" without SIMPLE_LLVM_BIN, llc on PATH
## Open 2026-10-31

- Severity: high for BuildRunner/Hello lanes that sanitize `SIMPLE_*`.
- Host: macOS aarch64. LLVM 23 at `/opt/homebrew/opt/llvm@23/bin`, which is on `PATH` and is
  not in `/usr/bin`.
- Compiler: Phase 3 lane rev8 stage2, sha256
  `adef5db249e4f2c2b17edeb93f4db89b279b7ddbe47c530e645a3e001d80ad45` (`wt-p3mono`, 1a36776c8de).

## Repro
`env -i PATH=/opt/homebrew/opt/llvm@23/bin:<timeout dir>:/usr/bin:/bin ... stage2 native-build
--entry test/fixtures/bootstrap/hello_sanity_matrix/single.spl ...` gives rc=1:
`AOT compile error ... reason: llc failed (exit -1)`. The kept IR compiles cleanly with the same
`llc` by hand. Adding `SIMPLE_LLVM_BIN=/opt/homebrew/opt/llvm@23/bin` gives rc=0, and the binary
prints `Hello, World!\n`.

## Suspects (not yet narrowed)
- `_find_tool_discover` (`src/compiler/95.interp/interpreter/llvm/tools.spl:136`). Its
  `command -v` arm returns the BARE name `llc`, and the AOT path may then spawn `llc` without a
  PATH search (exit -1 = spawn failure).
- Alternatively, the AOT path uses `find_llc_portable` (`70.backend/backend/llvm_capability.spl:190`)
  with a different probe order.

## Workaround
`scripts/bootstrap/hello-sanity-matrix.py` keeps an absolute, existing `SIMPLE_LLVM_BIN` across
its `SIMPLE_*` sanitization, tagged `@workaround bug=stage2_llc_discovery_ignores_path_2026-10-31`.
Remove that pass-through once discovery resolves an absolute `llc` from PATH.
