# Stale interpreter-extern-gap baseline blocks every hook-enabled push (2026-09-01)

## Symptom

A real hook-enabled `git push` (no `--no-verify`) stopped on:

```
check-interpreter-extern-registry-gap: FAIL — 232 symbol(s) checked, 0 new, 3 stale — stale: rt_host_gpu_active_backend_handle rt_list_dir rt_page_size
push-must-check: BLOCKING gate push-interpreter-extern-registry-gap failed (exit 1)
```

Pre-existing on unmodified `origin/main` (byte-identical verdict when re-run
against origin/main content). `0 new` — no new debt. All three are STALE
baseline rows: symbols that are no longer registry gaps but whose rows in
`scripts/check/interpreter_extern_gap_baseline.txt` were never retired.

While any blocking gate is RED on unmodified main, every push in the repo uses
`--no-verify`, which bypasses all 19 gates — so the 6 gates wired today
(PRs #278, #280) were inert.

## Per-symbol evidence and classification

| symbol | classification | evidence |
|---|---|---|
| `rt_page_size` | **now registered** | still declared at `src/compiler/90.tools/sffi_gen/specs/mmap_syscalls.spl:37`; static registry row added at `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1852` (`insert_simple!("rt_page_size", memory::rt_page_size);`). No longer a gap. |
| `rt_list_dir` | **declaration removed** | removed from `src/compiler` by `1f080d68c7d` ("lane L2 — remove unbacked rt_list_dir (silent-nil) for backed dir_list"), hunk `-extern fn rt_list_dir(path: text) -> [text]` in `src/compiler/35.semantics/any_escape/types.spl`. Zero `extern fn rt_list_dir` under `src/compiler/**` today; only `rt_list_dir_recursive` survives, in `src/lib/nogc_sync_mut/sffi/io.spl:292` (out of the guard's `src/compiler/**` scope, and a different name). |
| `rt_host_gpu_active_backend_handle` | **declaration removed** | removed from `src/compiler` by `07206ba1e37` ("fix(test-runner): execute specs in pure interpreter"), hunk `-extern fn rt_host_gpu_active_backend_handle() -> i64`. No `.spl` declaration anywhere in `src/` now; the name survives only in `src/runtime/runtime_native.c` and `src/compiler_rust/runtime/src/host_gpu_lane.rs`. |

**Guard-misreading branch ruled out.** The searches used were strictly broader
than the guard's own extractor (`^[[:space:]]*extern fn rt_[A-Za-z0-9_]+`), so
zero hits under the broad grep implies zero under the guard's. And the folded
`insert*!("rt_…"` extraction does see the `rt_page_size` row, so there is no
normalization bug either. The guard is correct; the baseline was behind.

## Root cause

`1f080d68c7d` retired the symbol's row from `scripts/check/unbacked_extern_baseline.txt`
(its commit message says "baseline line removed") but not from
`scripts/check/interpreter_extern_gap_baseline.txt` — a *different* baseline
tracking a *different* invariant. Two frozen-set ratchets can both name the same
symbol; retiring one row is not retiring the other. `07206ba1e37` and the
`rt_page_size` registration touched neither.

## Fix

Retired exactly those 3 rows from
`scripts/check/interpreter_extern_gap_baseline.txt` (79 -> 76 lines; `git diff`
shows 3 deletions, 0 insertions, no re-sort). The baseline was NOT regenerated
wholesale — `--generate-baseline` is for deliberate reviewed updates only, and
regenerating would have laundered any genuine new debt into the frozen set.

## Verification (exit status read into a variable on the line AFTER the command, never through a pipe)

Before, at origin/main:
```
check-interpreter-extern-registry-gap: FAIL — 232 symbol(s) checked, 0 new, 3 stale — stale: rt_host_gpu_active_backend_handle rt_list_dir rt_page_size
```

After:
```
check-interpreter-extern-registry-gap: PASS — 6 fixture(s) checked, selftest only        (rc=0)
check-interpreter-extern-registry-gap: PASS — 232 symbol(s) checked, 0 new, 0 stale      (rc=0)
```

The checked count is unchanged at 232 — it counts declared externs, which a
baseline edit cannot move. A PASS at 229 would have meant something else moved.
