# compiler_cli_build crashes 0xC0000005 in native_staged at ~60.8 GiB commit (c43full)

Date: 2026-11-19
Host: Windows 11, x86_64-pc-windows-msvc
Lane: criterion-2 full bootstrap cycle 7, pinned 9ec993816375, authorized run
c43full (receipt 5ef58caaf19b…), stage2 slim verification matrix

## Observation

compiler_cli_build progressed FURTHER than any prior cycle: HIR complete
(jit_sffi poison fixed by PR #10327), AOP weave complete, native_cache
complete, then died during `phase=native_staged` at batch-58 (464/4008
modules) with no in-log error:

```
verification/campaign.RvYGFa/process.env:
  status=complete  exit_status=1  root_exit_raw=0x1
  abnormal_exit_ntstatus=0xc0000005        # ACCESS VIOLATION
  peak_job_commit_kib=63791940             # ~60.8 GiB tree commit peak
  job_members_peak=16
```

Campaign ran 3h06m of an 8h budget (not a timeout); watchdog sampling stayed
healthy (no rss-measurement failure — the PR #10245 retry patch held).
VERDICT ABORTED stage-engine-failed; same 4 missing PASS rows as cycles 5–6
but now caused by a native crash, not HIR diagnostics.

## Memory trajectory (in-log)

```
[mir] 300/4008 rss_mib=34116 elapsed_s=968
[mir] 350/4008 rss_mib=35964 elapsed_s=1091
[mir] 400/4008 rss_mib=37728 elapsed_s=1266
[mir] 450/4008 rss_mib=38151 elapsed_s=1437   # still climbing
```

MIR-phase RSS grows ~4 GiB per 50 modules early; by native_staged the job
commit peaks at 60.8 GiB — above the 56 GiB watchdog cap, which is
monitor-only (phys_footprint_cap_enforced=0), so nothing throttles it.
The crash plausibly follows unchecked allocation failure at extreme commit
(Windows malloc/VirtualAlloc failure → null deref) or a genuine UAF.

## Related tracked classes

- pure_simple_native_codegen_rss_growth_2026-10-21.md
- phase3_mir_retained_memory_2026_10_17.md
- stage3_closure_loop_rss_growth_after_provider_feed_2026-10-20.md
- mir_lower_child_tasks_append_access_violation_2026-10-19.md

## Candidate fix in flight (other lane)

PR #10334 (open at observation time): guards `rt_array_free(sorted)` behind
`owns_sorted` (caller-owned rows never freed on merge pass 1), pre-validates
surface aliases/import item bounds before retiring arrays, clears replaced
fields to `[]` before `rt_array_free`, and defaults P3G_ENTRY_MIR_SHARDS —
direct UAF + MIR-retention relevance. Re-run this gate on a pin that includes
it before deeper instrumentation.

## Next steps if it still crashes after #10334

1. Reproduce the native_staged crash standalone with the stage-2 driver on
   the full-cli closure and capture a WER dump (LocalDumps) for a stack.
2. If allocation-failure-on-Windows: audit the codegen batch allocator for
   unchecked null returns; if UAF: the #10334 guard sites are the first
   suspects to extend to native_staged batch boundaries.
3. Consider per-batch process isolation for native_staged to cap commit
   (currently serial in-process batches of 8 modules retain state).

Evidence: c43full/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/
{campaign.RvYGFa/process.env, logs/compiler_cli_build.log} in the v8 lane tree.
