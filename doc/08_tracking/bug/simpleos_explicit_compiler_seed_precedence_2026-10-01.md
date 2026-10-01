# OS builds preferred Rust seeds over an explicit compiler

Status: source fix authored in the isolated items 1/5/7 tree; runtime acceptance
and generated manuals remain TEST_BLOCKED. No landing or feature PASS claimed.

The isolated baseline's `_find_simple_binary_for_target` probes Rust bootstrap
and release seeds before `SIMPLE_BINARY` on LLVM routes. Its other fallback
lists also include seeds. Its backend probe invokes an invalid target but
expects an unrelated invalid-mode diagnostic, while an existing canary helper
does not supply the selected backend. This blocks trustworthy live CLI route
acceptance even when a self-hosted compiler was explicitly selected.

The compiler capability owner was already corrected in the clean C-tree file
`src/os/_QemuRunner/os_build_run.spl` at commit
`ca713ba9e0c7b5f5ee0858550a64d6c38244409a` (inspected at detached HEAD
`b7c3552a6940d9459eb83e15929619f5c90d8eb2`). This slice adapts its existing
`simpleos_candidate_version_is_selfhosted`,
`simpleos_compiler_candidate_supports_backend`,
`simpleos_select_compiler_candidate`, and executable LLVM canary contract.
The C-tree is untouched; unrelated changes are not imported.

The new `os.qemu_compiler_admission_v1` facade delegates explicit admission to
canonical deployed-runtime or full-CLI Stage4 provenance and implicit discovery
to the canonical release-runtime selector. `SIMPLE_BINARY` takes precedence
over `SIMPLE_BIN`; a refused explicit artifact never selects another binary.
Only the admitted path enters backend-capability checks, and the actual OS
compiler process inherits the existing pinned identity environment. Empty
selection fails before output preparation or native compilation. Native secure
temporary directories keep the LLVM canary independent of POSIX `/tmp` path
assumptions on Windows.

The focused unit checks policy/refusal. The new live CLI-route system spec
requires a real admitted compiler and existing kernels/media, compares actual
CLI inspection/run behavior and separately checks real guest serial markers.
It never requires removing bootstrap seeds. Verification still requires both
host lanes, existing backend-canary units, rebuilt CLI, docgen and maintenance
scan. Existing broader runner source-shape checks include pre-existing
unrelated facade-migration expectations; no all-runner PASS is asserted.
