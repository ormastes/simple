# tauri mobile MDI input-to-paint validator hangs 60s+ on malformed rows

Date: 2026-07-04
Status: open
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
