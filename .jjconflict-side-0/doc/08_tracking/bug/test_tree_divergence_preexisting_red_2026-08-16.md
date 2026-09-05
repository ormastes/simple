# Pre-existing test-tree divergence red at `f6cadcc36af` — step-over record

**Status:** OPEN (pre-existing; not introduced by this session)
**Recorded:** 2026-08-16, as the mandatory record accompanying a delta-PASS landing
per `.claude/rules/vcs.md` ("Landing on a delta-PASS additionally REQUIRES recording
the pre-existing offender list ... an unrecorded step-over is a violation even when
the delta is clean")

## Why this record exists

`scripts/check/check-test-tree-divergence.shs --ref <NEW>` is RED at
`f6cadcc36aff61d16d988651ea36a040d2af6aad` (== `origin/main`):

```
FAIL — 828 diverged vs 814 baselined (15 new, 1 fixed-but-still-baselined);
2 mirror-only (0 unallowlisted, 0 stale-allowlist)
```

The landing it accompanies (`docs(bug)` x2, `doc/08_tracking/bug/` only) touches **zero**
test files, so it cannot have contributed. Confirmed mechanically rather than by
assertion:

```
check-test-tree-divergence-delta.shs f6cadcc36aff61d16d988651ea36a040d2af6aad 7a54b976ae1
  -> pre-existing red is identical at BASE and NEW; this range introduces nothing
  -> PASS — 16 pre-existing offender(s), 0 introduced by this range
```

## The 16 offenders

15 diverged but not baselined ("new"):

```
integration:rendering/vulkan_strict_spec.spl
unit:compiler/60.mir_opt/hwir_opt_spec.spl
unit:compiler/borrow/borrow_check_spec.spl
unit:compiler/deep/borrow_check_move_1_spec.spl
unit:compiler/verification/lean_basic_spec.spl
unit:compiler/verification/lean_codegen_spec.spl
unit:compiler/verification/lean_workflow_spec.spl
unit:compiler/verification/report_rendering_spec.spl
unit:compiler/verification/tool_checker_spec.spl
unit:compiler/verification/unified_attrs_spec.spl
unit:os/kernel/arch/riscv64_syscall_ipc_spec.spl
unit:os/kernel/arch/x86_64_interrupt_spec.spl
unit:os/kernel/ipc/syscall_number_consistency_spec.spl
unit:os/services/vfs/vfs_chmod_symlink_spec.spl
unit:os/sosix/io_spec.spl
```

1 baselined but now identical (stale baseline entry):

```
unit:lib/nogc_async_mut/async_host_spec.spl
```

## Not fixed here

Resolving these means reconciling the duplicate test trees (`test/01_unit/` vs
`test/unit/`, `test/02_integration/` vs `test/integration/`) pair by pair, or — for the
stale entry — removing the line from
`scripts/check/test_tree_divergence_baseline.txt` after confirming the pair really is
identical. Neither is this session's lane (an SCV file-read/rendering coverage review),
and `--generate-baseline` must not be used to paper over the 15 new entries without
reading each diff.

Note `integration:rendering/vulkan_strict_spec.spl` and
`unit:compiler/verification/report_rendering_spec.spl` fall in the rendering area this
session reviewed; they are listed here as divergence offenders only — no claim is made
about their content.
