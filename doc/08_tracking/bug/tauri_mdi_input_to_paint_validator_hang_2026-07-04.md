# tauri mobile MDI input-to-paint validator hangs 60s+ on malformed rows

Date: 2026-07-04
Status: closed 2026-11-13 — no validator hang; file-level watchdog misattributed (see Resolution)
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

## Resolution (2026-11-13)

Host: DGX Spark GB10 aarch64, Rust seed (sha256 `af717f53d6bce3e5…`), base
`2a2412399b5` (release/1.0.0), each run under `MemoryMax=16G timeout 900`.

**The validator does not hang.** The named example alone (one-example copy of
the spec) passes in 3 s wall; inside the full 40-example file it passes too.
The lane is fixture-driven (`node` + `sh`), so it is not display/webview
blocked.

**What the July report actually saw.** `[PERF BUG]` is a per-FILE tag
(`src/compiler_rust/driver/src/cli/test_output.rs:75`, `file.duration_ms >=
60000`), not a per-example one. The July spec (`7c30ce49d04`) already had 40
examples and "rejects malformed mobile MDI input-to-paint detail rows" was the
26th. Every example shells out to the whole aggregate gate once or twice
(~1.4 s each here), so "25/26 pass, the 26th exceeds 60 s" is the cumulative
file budget expiring while example 26 happened to be in flight. No
non-advancing loop was found or needed in
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`; it is
unchanged by this fix.

**The real defect found (and fixed).** The tracked spec was red for a
different reason: `88aac2ffe28` (2026-09-29 tree transplant) rewound its
helpers and example bodies to a pre-`eb17b8ded20` snapshot while keeping
newer call sites, so `_run_aggregate_command` took 3 arguments but was called
with 5 and `_run_aggregate_command_with_logs` did not exist. Fix: restore the
`eb17b8ded20` helpers and bodies under the current header and per-example
`@req`/`@capture`/oracle annotations, and correct two stale Android fixture
sizes (declared coherent-source size 49 -> 74 bytes, the real `android.log`
size) in the symlinked/hardlinked coherent-source examples.

| state | result | wall |
|---|---|---|
| RED, tracked spec at `2a2412399b5` | `executed=40 passed=1 failed=39` (semantic: "expects 3 argument(s), but 5 were provided") | 2 s |
| helpers+bodies restored, sizes not yet fixed | `passed=38 failed=2` | 55 s |
| GREEN, this change | `outcome=OK executed=40 passed=40 failed=0` | 54.4 s (`Duration: 54417ms`) |

**Residual (not fixed here).** The file needs ~54 s on this host at load ~7,
so it sits 10% under the 60 s `[PERF BUG]` threshold and will be tagged again
on a slower or busier host. That is file size (40 process-heavy examples), not
a hang; the remedy is splitting the spec or caching the generated PNG fixture,
not a validator change.
