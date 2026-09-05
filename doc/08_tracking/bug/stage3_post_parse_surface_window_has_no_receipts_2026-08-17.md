# Stage 3: the post-parse module-surface window emits no progress receipts

- **Date:** 2026-08-17
- **Status:** OPEN (mitigated — receipts added; the underlying ~30-minute cost is not fixed)
- **Component:** `src/compiler/80.driver/driver_source_pipeline_parsing.spl`

## Symptom

Stage 3 (`native-build ... src/app/cli/bootstrap_main.spl`) appeared hung:

- stage3 log frozen at 48,680 bytes for 30+ minutes
- last line `[build] parse 619/619 step 1/6 src/std/nogc_sync_mut/io/sffi_common.spl`
- events file: `phase=parse ... done=619 ... tasks_done=1 tasks_total=6`
- **`phase=hir` never recorded**
- ~72% of one core, RSS flat at 7.97 GB

It was read as a hang, and as a suspected regression from the re-entrancy
breaker `cffc414c2de` in `register_imported_type_methods`.

## It is not a hang, and not that guard

Measured against the live process (pid 3078423, running from
`/mnt/data/worktrees/simple-boot-snap`, binary
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`):

| observation | value | what it rules out |
|---|---|---|
| `[stack]` VMA in `/proc/PID/smaps` | **132 kB** | deep recursion. The prior SIGSEGV had `rsp` on a guard page 8 MB down a worker stack; here the main thread has touched 132 kB total, so the guard's stack depth `d` is bounded at roughly a hundred frames. A quadratic-in-`d` guard cannot cost 30 minutes. |
| `Threads` | **1** | any thread-pool / worker interaction, despite `--threads 8` |
| `[heap]` VMA growth | **13.5 kB/s** (0x21000 per 10 s, three consecutive samples) | allocation-heavy churn. This process's allocations accumulate in RSS — the comment at `driver_source_pipeline_parsing.spl:319-325` records a prior variant of this code growing RSS 1.5 GiB per 30 s — so 13.5 kB/s of heap growth *is* the allocation rate. The guard interpolates a fresh `text` key and rebuilds a fresh `[text]` per call; at any rate that could cost 30 minutes it would move hundreds of MB/s. |
| minor faults | 3.5/s | same |
| **it finished** | at `elapsed_s=2404` the events file advanced to `tasks_done=2`, main log 48,680 -> 362,229 bytes, RSS 7.98 -> 14.34 GB | that it was stuck at all |

**The `imported_type_methods_in_progress` guard hypothesis is REFUTED.** The
guard (`_Items/module_lowering.spl:1505-1516`, accessors at
`hir_lowering/types.spl:313-327`) is `O(d)` per call with a small `d`, and in
any case the process had not reached HIR lowering yet — which is exactly what
"`phase=hir` never recorded" was telling us, and was misread as "stuck in HIR".

Main already routes the guard through the
`imported_type_methods_in_progress_has/_push/_pop` accessors, so the
accessor-migration half of the proposed fix was already done. No guard change
was made: the pop's filter-and-rebuild is `O(d)` on a `d` of order 100, off any
hot path, and editing it on no evidence would be churn in a tree ~16 bootstrap
lanes share.

## The actual defect

The window between the last per-file parse receipt
(`driver_source_pipeline_parsing.spl:316`) and the `parse`/`modules` receipt
(`driver_orchestration.spl:134`) emitted **nothing**, while containing four
substantial sub-steps:

1. 619 x `entry_surface_builder.add_parsed(...)` plus `entry_modules[...] = ...`
2. the alias pass over `entry_sources` (`add_alias`)
3. `resolve_export_origins()`
4. `finish()` / `module_surfaces_by_name_from_parts`

30+ minutes elapsed in there with no way to say which sub-step, because
attach-based profiling is blocked on this host (`ptrace_scope=1`,
`perf_event_paranoid=4`) — `gdb -p` returns "Could not attach to process".
This is the same class of defect as
`stage3_parse_stalls_at_tail_43_files_2026-08-17.md`, one phase later, and the
same remedy applies.

## Change

Added receipts to that window, following the per-unit precedent the parse loop
already set (`phase=surface_build`, `surface_alias`, `export_origins`,
`surface_freeze`). A stall in this window now names its sub-step, and
`surface_build`/`surface_alias` name the individual source.

Verification of the edit: the Rust seed (`bin/simple`, mtime 2026-08-16 22:59 —
stale seed, and the only binary used for this check) compiles the module clean
via an import probe. **Control run**: appending a deliberate syntax error to the
module makes the same probe print `[WARN] Failed to load imported types ...
Failed to parse module`, proving the probe actually parses this file and that
the clean result is not vacuous. Note the probe's exit code is 0 either way —
the WARN line, not `rc`, is the signal. `bin/simple fmt --check` is not usable
as a gate here: it reports `formatter rejected lexically invalid source` on the
**unmodified** file from `git show HEAD:` too.

## Still open

Why the window costs ~30 minutes at all. `resolve_export_origins` is already
dict-indexed and near-linear, and the measured allocation rate during the stall
was ~13.5 kB/s, so the cost is a compute-bound, allocation-free loop —
plausibly Dict insert probing at scale, or a per-item linear scan. The next
stage-3 cycle will name the sub-step from the new receipts; that is the
prerequisite for fixing it.

## Status re-check 2026-08-17 — STILL OPEN (mitigation confirmed in tree)

binary identity: `readlink -f bin/simple` = `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`; `stat -c '%s %y'` = `59537240 2026-08-17 12:58:51.339525019 +0000`

The receipts half of this record is present in the current tree:

```
$ grep -n "surface_build\|surface_alias\|export_origins\|surface_freeze" \
      src/compiler/80.driver/driver_source_pipeline_parsing.spl
343:  log_build_progress("surface_build", "files", 0, ...
393:  log_build_progress("surface_build", "files", ...
396:  log_build_progress("surface_alias", "aliases", 0, ...
421:  log_build_progress("surface_alias", "aliases", entry_alias_done, ...
423:  log_build_progress("export_origins", "surfaces", 0, -1, ...
```

The "still open" half — why the window costs ~30 minutes — is unchanged and was
not measured here: naming the sub-step requires a stage-3 run to emit these new
receipts, and a bootstrap was out of scope for this session. Nothing changed.
