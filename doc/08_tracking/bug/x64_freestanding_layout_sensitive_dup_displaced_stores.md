# BUG: freestanding module frame-builder emitted duplicated slot stores with +16 displacement — layout-sensitive codegen corruption

**Status:** open (reproduced once with real dumped bytes; vanishes with unrelated code motion)
**Severity:** high when it strikes (silent memory corruption), low reproducibility (layout-sensitive)
**Component:** native-build freestanding codegen — suspected var-reassignment / loop-carried-variable lowering
**Found:** 2026-07-12 (clang bisection lane, Build A vs Build B)

## Symptom

In one build (Build A of the bisection series), the SysV frame builder in
`src/os/kernel/loader/x86_64_fs_exec_ring3.spl` emitted DUPLICATED stores for
frame slots 0/1 and displaced every later store by +16 bytes — observed via
rt_dump_phys16 ground-truth dumps of the actual frame memory (not readback
artifacts). Adding unrelated code to the entry file (Build B) made the
corruption vanish and the same builder produced byte-identical-to-reference
frames.

## Why this matters

This is a second independent sighting of layout-sensitive freestanding
miscompilation (same family as
`x64_freestanding_mmio_read_u8_address_dependent_zero.md`): correctness of
emitted stores depends on unrelated code in the compilation unit. Signature
points at var-reassign/loop-carried-var SSA handling in the loop that walks
argv/envp slots.

## Repro pointer

BISECT_NOTES.md (lane worktree agent-a453cd3a7bc8bbf4b) Builds A/B; run logs
buildA_run.log / buildB_run.log in the session scratchpad. Frame dump deltas
are recorded in the notes. No minimal repro yet — extraction of a standalone
case (module fn with loop-carried slot pointer + reassignment, compare dumped
stores across padding variants) is the next step.

## Verification note 2026-08-17 (BLOCKED, NOT a close)

This row cannot be settled by static grep, and that is expected, not a gap
in this pass: the defect is defined as "the SAME source in `x86_64_fs_exec_ring3.spl`
compiles to different, sometimes-corrupt frame stores depending on UNRELATED
code elsewhere in the same compilation unit" — there is no fixed string,
constant, or branch pattern to search for in `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`
that would prove presence or absence; the bug is a property of the codegen's
output for a specific `.bss`/frame layout, observable only via a real dumped
frame (`rt_dump_phys16`) compared against expected bytes for that exact build.
No such dump was reproduced this pass (no rebuild/QEMU boot attempted).
Harness needed to settle this: (1) rebuild the freestanding x86_64
`x86_64_fs_exec_ring3.spl` kernel via `native-build --target x86_64-unknown-none
--backend cranelift`, (2) boot under QEMU/OVMF real-firmware per
`.claude/rules/board-runnable.md`, (3) capture `rt_dump_phys16` frame bytes at
the argv/envp slot region, (4) diff against a known-good reference frame.
Status: BLOCKED, unchanged from doc. Not upgraded to resolved.
