# Stage 2 AOT fails "llc failed (exit -1)" without SIMPLE_LLVM_BIN, llc on PATH
## Resolved 2026-10-31

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

## Root cause
The AOT object path `compile_ir_to_object_path`
(`src/compiler/70.backend/backend/llvm_backend_tools.spl`) calls `find_llc()` and then spawns the
result with `process_run(tool, args)`, which does not search PATH. `find_llc` goes through
`_find_tool_discover` (`src/compiler/95.interp/interpreter/llvm/tools.spl`). With
`SIMPLE_LLVM_BIN` unset and no `/usr/bin/llc`, its `command -v` arm answered with the BARE name
`llc`, so the spawn failed with exit -1. `find_llc_portable` (`llvm_capability.spl`) was not the
cause: it already resolves an absolute path in process through `backend_tool_on_path`.

## Fix
`_find_tool_discover` replaces the `command -v` arm with `backend_tool_on_path([candidate])`, the
in-process PATH walk shared with `find_tool_portable` (`:` on POSIX; the working directory, `;`
and PATHEXT on Windows). It returns the hit only when the path is absolute (`/...`, `C:\...`,
`C:/...`, UNC) and `--version` runs. A relative PATH entry falls through to the existing Windows
`where` loop and the Homebrew probes. The pass-through in `scripts/bootstrap/hello-sanity-matrix.py`
is removed. That covers `inherited_build_settings` no longer keeping `SIMPLE_LLVM_BIN` and the
`llvm_bin_identity` identity fields.

## Test
`test/01_unit/compiler/95.interp/interpreter/llvm/tool_discovery_path_spec.spl` puts a fixture
tool on PATH and asserts that `_find_tool_discover` returns its absolute, existing path. Red
before the fix (it returned the bare name), green after. `test/01_unit/compiler/backend/llvm_tool_resolution_spec.spl`
and `scripts/bootstrap/tests/hello-sanity-matrix-env-test.py` still pass. End-to-end Stage 2
`native-build` re-verification without `SIMPLE_LLVM_BIN` is still pending a Stage 2 rebuild that
includes this fix.
