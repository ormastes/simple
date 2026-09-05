# StarFive DTB policy RV64 freestanding object emission is unavailable

Status: open

The Rust bootstrap seed can emit and execute the exported policy as a hosted
x86-64 shared object, and the mixed C/Simple harness passes all six production
branch outcomes. Its `compile --native --shared --target
riscv64-unknown-simpleos` route nevertheless invokes a hosted link and fails
with `unable to find library -lc`; the legacy compile command has no
relocatable-object option. The newer pure-Simple `native-build --emit-object`
source route, executed by the currently deployed source-mismatched Rust-hosted
Simple binary, reaches code generation but fails with `semantic: type mismatch:
cannot convert object to int`. No admitted source-matched pure-Simple compiler
evidence exists yet.

Acceptance requires a source-matched admitted pure-Simple compiler to emit a
freestanding RV64 relocatable object containing `starfive_dtb_policy_select`,
then link it with the compiled `starfive_runtime.c` object and the board linker
script without libc. Hosted mixed-link evidence is diagnostic only.

The source candidate removes the policy's `bool as u64` conversion, replacing
it with explicit outcome-index control flow. A fresh minimal projection using
only `src/os/kernel/arch/riscv64/starfive/boot` nevertheless still reaches the
same `semantic: type mismatch: cannot convert object to int` diagnostic after
parsing and lowering with that source-mismatched Rust-hosted binary. This
proves the remaining failure is not caused by source-closure breadth, but does
not localize the stale compiler defect further. The C runtime now reads only
candidate and fallback magic
scalars and delegates the selection decision to the unchanged exported
`starfive_dtb_policy_select` ABI. Final RV64 object/link acceptance remains
deferred until a source-matched admitted pure-Simple compiler exists.
