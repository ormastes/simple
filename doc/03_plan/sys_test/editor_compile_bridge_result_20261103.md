# Editor JIT compile bridge failure contract

Bug: `editor_jit_run_route_blockers_2026-05-28` remains OPEN.
Baseline: `d591d1df36f4bad9692c8eeab65c1a3a7ba69e6e`.

REQ-EDITOR-JIT-001 requires the optimized public compile facade to return a
readable `(false, diagnostic)` tuple when compilation cannot be performed.
The integration spec calls the real facade with a missing source at optimization
levels zero, two, and invalid. It inspects both tuple fields; merely returning
from the extern is not success. These inputs must not start a compiler build.

The ordinary facade already has missing-source assertions in
`test/01_unit/sffi/sffi_public_api_spec.spl`; this spec covers its optimized
sibling. Run interpreter and native/JIT variants separately with admitted,
source-matched producers and linked runtime identities. An interpreter-only
PASS cannot qualify the native runtime bridge.

## Prior fixes and remaining boundary

- `gui_shell_run_sdl_profile` already annotates `state: GuiShellState`; do not
  reapply the historical masking-inference workaround.
- Runtime alias mapping and its regression cases already exist in the Rust
  code generator; no alias patch is justified by the old report alone.
- `src/compiler_rust/runtime/src/value/cli_sffi.rs` exports the two compile
  functions but returns literal integer zero. The public Simple declarations
  require a tagged tuple. The interpreter-host implementation in
  `interpreter_extern/native_sffi.rs` has a separate real compile path.
- A native failure-result repair does not implement a JIT-to-compiler driver
  bridge or prove editor launch, file-watcher VReg behavior, or successful
  compilation. Those original acceptance criteria remain unresolved.

## Evidence limits

Spec-first commit: `8b9f27f7eed`.
Direct Rust owner tests first: `d425926be32`.
RED: NOT RUN. GREEN: NOT RUN. Coverage: UNMEASURED. Docgen: NOT RUN.
No admitted Simple runtime was available; no compiler/seed/bootstrap build or
fallback was attempted. No bug status or tracker row may be closed from this
source-contract work. At most two implementation/verification cycles per cause.

## Bounded source repair

Both Rust runtime exports retain their existing `i64` return ABI and symbol
names. They now return the raw bits of a real runtime tuple containing tagged
`false` and an unavailable-driver diagnostic. No process is spawned, no compiler
is delegated to, and no output artifact is fabricated. Standard runtime
allocation failure remains NIL; a failed tuple allocation frees its diagnostic.

`RuntimeValue` is `repr(transparent)` over `u64`; the codegen declarations already
use one `I64` result. Direct Rust assertions decode those bits with `from_raw`,
require tuple length two, verify boolean tagging and false, and inspect the real
runtime string. Those tests are authored, not executed.

This provider is `src/compiler_rust/runtime`, not `src/runtime`'s current C
provider. No equivalent C export was found in the scoped search. The patch
therefore repairs only the Rust provider's unavailable-result representation;
the canonical editor JIT bug and current self-hosted C-native qualification stay
OPEN. No C signature changed, so the on-demand C-contract compilation does not
exercise these Rust exports and is not claimed as verification.
