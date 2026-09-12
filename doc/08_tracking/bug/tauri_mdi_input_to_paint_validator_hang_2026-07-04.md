# tauri mobile MDI input-to-paint validator hangs 60s+ on malformed rows

Date: 2026-07-04
Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
Severity: P3 (validator edge case; 25/26 sibling examples pass instantly)
Found by: fable orchestrator, G5 evidence batch (honest post-greenwash runner)

## Symptom

`test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl`
example "rejects malformed mobile MDI input-to-paint detail rows" exceeds the
60 s wall-clock watchdog (runner tags it `[PERF BUG]`; crash report
`.simple/logs/crash_2159615.log`). All 25 other examples in the spec,
including the adjacent "rejects malformed mobile MDI performance and
animation detail rows", pass in <2 s. Reproduce:

```sh
CAP_MEM_MAX=2G scripts/resource/run_capped.shs bin/simple test --clean \
  test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl \
  --no-session-daemon --sequential
```

## Suspected shape

Pathological loop in the input-to-paint detail-row validator on malformed
input (its sibling validators reject the same class of input instantly).
Possibly previously masked by the pre-2026-07-03 test-runner greenwash
(file-level `Failed: 0` on red describes).

## Next steps

- Bisect the validator's malformed-row loop (likely an index that never
  advances on a row that fails to split).
- Add a per-example timeout guard tighter than the 60 s file watchdog for
  validator-only specs.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
