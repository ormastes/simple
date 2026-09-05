# 4edef8fab8 stale-snapshot clobber: 458 files still unrepaired, 32,530 lines missing

**Date:** 2026-08-27
**Offending commit:** `4edef8fab8` "feat: snapshot current development state"
(2026-08-26 01:21) — **11,225 files, +1,275,284 / −860,823**
**Status:** OPEN — one portion repaired (20.hir callable dependency), the rest unaudited until now
**Severity:** critical — it is an ANCESTOR of `origin/main`, so the deletions are live

## What it is

A stale whole-working-copy snapshot pushed over `main` — the exact anti-pattern
fenced by `.claude/rules/vcs.md` § "Sync must never clobber". It did not merge;
it replaced tracked content with an older working copy, silently reverting
landed fixes from other sessions.

**It compiles.** That is why it went unnoticed: in the Stage-3 case only the
CALLER of a surviving helper was deleted, so nothing failed to build and no gate
fired. `check-tree-size-push.shs` cannot see it either — the tree GREW (11,225
files touched, net +414k lines), so a file-count band is blind by construction.

## Confirmed consequence #1: the Stage-3 wall

Stage 3 self-host stops at module **261/713** with `ambiguous explicit callable
dependency`. That is not a new defect — it is the 2026-08-21/22 fix
(`stage3_callable_dependency_named_glob_precedence_2026-08-21.md`) having been
deleted. Symbol counts in
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`:

| symbol | `4edef8fab8~1` | `origin/main` |
|---|---|---|
| `canonical_callable_dependency_candidate` | 3 | **0** |
| `selected_rank` (explicit>glob tier) | 7 | **0** |
| `hir_ambig_dep_trace` | 33 | **0** |

Independently reproduced by the parent session with
`git show <rev>:<path> | grep -c`.

## Audit of what is STILL missing (2026-08-27)

Comparing `4edef8fab8~1` against `origin/main` for every `src/` file the
snapshot reduced:

- **458 files still hold less content than before the snapshot**
- **32,530 lines still missing**
- **56 files are absent from the tree entirely; 54 of those are genuinely
  deleted, not moved** (verified by searching the whole tree for each basename —
  2 of the 56 were relocated and are NOT losses)

Regenerate this list exactly:

    git diff --numstat 4edef8fab8~1 4edef8fab8 -- 'src/**' | awk '$1<$2 {print $3}' |
    while read f; do
      pre=$(git show 4edef8fab8~1:$f 2>/dev/null | wc -l)
      hd=$(git show origin/main:$f 2>/dev/null | wc -l)
      [ "$pre" -gt 0 ] && [ "$hd" -lt "$pre" ] && printf '%d\t%d\t%d\t%s\n' $((pre-hd)) $pre $hd "$f"
    done | sort -rn

### Worst 25 by lines still missing

| path | before | at HEAD | missing |
|---|---|---|---|
| src/os/installer/image_builder.spl | 2103 | 798 | 1305 |
| src/os/apps/servers_user/http1_request_frame_owner.spl | 1174 | 0 | 1174 |
| src/runtime/runtime_native.c | 13839 | 12798 | 1041 |
| src/lib/nogc_async_mut/fs_driver/mount_table.spl | 1676 | 799 | 877 |
| src/compiler/20.hir/generated/hir_codec.spl | 6981 | 6232 | 749 |
| src/compiler_rust/compiler/src/native_build_sffi.rs | 735 | 0 | 735 |
| src/os/apps/sshd/ssh_session_channel.spl | 1450 | 773 | 677 |
| src/os/kernel/scheduler/server_data_launch_grant_registry.spl | 662 | 0 | 662 |
| src/compiler_rust/compiler/src/interpreter/node_exec.rs | 3627 | 3127 | 500 |
| src/os/kernel/scheduler/process_execution_observation.spl | 609 | 137 | 472 |
| src/os/apps/sshd/arm64_ssh_request_context_owner.spl | 445 | 0 | 445 |
| src/compiler/35.semantics/lint/cow_alias_hotpath.spl | 408 | 0 | 408 |
| src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl | 1397 | 1003 | 394 |
| src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl | 804 | 414 | 390 |
| src/compiler_rust/compiler/src/interpreter/sampler.rs | 385 | 0 | 385 |
| src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl | 4866 | 4501 | 365 |
| src/lib/nogc_sync_mut/spec/in_development.spl | 363 | 0 | 363 |
| src/compiler/80.driver/driver_hir_pipeline_lowering.spl | 1319 | 994 | 325 |
| src/compiler_rust/common/src/engine_receipt.rs | 315 | 0 | 315 |
| src/lib/nogc_sync_mut/tag_query/dev_id.spl | 298 | 0 | 298 |
| src/os/apps/servers_user/main.spl | 556 | 270 | 286 |
| src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl | 680 | 402 | 278 |
| src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl | 831 | 561 | 270 |
| src/lib/common/contracts/os/server_data_namespace_v1.spl | 268 | 0 | 268 |
| src/os/kernel/scheduler/scheduler_task_mgmt.spl | 628 | 364 | 264 |

### Sample of files deleted outright (54 total, verified absent tree-wide)

- `src/os/apps/servers_user/http1_request_frame_owner.spl`
- `src/compiler_rust/compiler/src/native_build_sffi.rs`
- `src/os/kernel/scheduler/server_data_launch_grant_registry.spl`
- `src/os/apps/sshd/arm64_ssh_request_context_owner.spl`
- `src/compiler/35.semantics/lint/cow_alias_hotpath.spl`
- `src/compiler_rust/compiler/src/interpreter/sampler.rs`
- `src/lib/nogc_sync_mut/spec/in_development.spl`
- `src/compiler_rust/common/src/engine_receipt.rs`
- `src/lib/nogc_sync_mut/tag_query/dev_id.spl`
- `src/lib/common/contracts/os/server_data_namespace_v1.spl`
- `src/os/services/vfs/server_data_virtio_probe.spl`
- `src/compiler/10.frontend/cache_dir_evict.spl`
- `src/os/kernel/arch/riscv64/fw_cfg_named_file_v1.spl`
- `src/os/port/init/compiler_filesystem_guest_workflow_v2.spl`
- `src/compiler_rust/compiler/tests/native_build_and_alias_symbols_registered.rs`
- `src/os/kernel/arch/arm64/fw_cfg_named_file.spl`
- `src/lib/common/contracts/os/server_data_media_v1.spl`
- `src/os/port/init/compiler_filesystem_metadata_v2.spl`
- `src/os/kernel/loader/executable_launch_arguments_v1.spl`
- `src/os/kernel/fw_cfg/x86_64_named_reader_v1.spl`

Deleted-file concentration by area: `src/os/kernel` 12, `src/compiler_rust/compiler` 12,
`src/os/apps` 3, `src/lib/nogc_sync_mut` 3.

Two deletions deserve specific attention:

- **`src/compiler/35.semantics/lint/cow_alias_hotpath.spl` (408 -> 0)** — the
  COW-alias LINT, sibling of `scripts/check/check-cow-alias-hotpath.shs`. The
  gate was widened on 2026-08-26 while its in-compiler counterpart was already
  deleted. Anyone reading the gate as full coverage is wrong.
- **`src/runtime/runtime_native.c` is 1,041 lines short** of its pre-snapshot
  state. It was edited on 2026-08-26 (a `_GNU_SOURCE` fix) on top of a
  clobbered base, so that file is a repaired-but-still-reverted generation.

## Why the existing guards did not stop it

Every pre-push guard is a structure check, and this commit is structurally
perfect: no conflict trees, no marker text, correct file count (it GREW), no
mass `rt_*` symbol removal, and it compiles. `check-no-revert-push.shs` needs an
exact blob match against ONE prior commit; a stale-forward snapshot is not an
exact revert of anything. The one control that would have caught it is the
manual rule in `.claude/rules/vcs.md`: *never whole-WC-commit files this session
did not change.*

## Repair status

- **20.hir callable dependency** — restored surgically in a lane (byte-identical
  to `4edef8fab8~1`), deliberately NOT by reverting the snapshot hunk, which
  would have undone the later constant-time `visited_depth` fix (`808f5cc2dd`,
  measured 9.57x). **Restore is content-verified but its effect on the 261/713
  wall is UNMEASURED** — the repro run died in parse at 40/124 and 43/124,
  recorded as UNKNOWN, not clean.
- **Nine post-snapshot commits** are already piecemeal repairs of this same
  clobber (one titled `...clobbered by 4edef8fab8e`). They were uncoordinated;
  no one held the whole list until this audit.
- **The other 457 files are unrepaired and unowned.**

## Do NOT "fix" this by reverting the snapshot

A wholesale revert would undo every genuine change that landed after it,
including the 9.57x re-export fix. Repair must be per-file, restoring from
`4edef8fab8~1` only where HEAD has no newer intentional change. The list above
is the work queue, not a patch.
