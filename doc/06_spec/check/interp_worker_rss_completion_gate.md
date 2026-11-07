# Interpreted worker RSS completion admission

Owner: `scripts/check/check-interp-worker-rss-budget.shs`.

The no-argument source worker's actual first main branch rejects callers without SIMPLE_NATIVE_BUILD_WORKER=1, prints `error: native_build_worker.spl is an internal entrypoint`, and exits1. The RSS probe now pins that variable to0. This measures import-closure loading followed by that expected refusal; it does not qualify an admitted worker request, backend initialization or native compilation.

Before numerical budget judgment, require measurement-wrapper status1, summary child exit1, exactly one valid final peak-rss summary and exactly one expected worker diagnostic as the last nonblank line before that summary. A crash, signal, unexpected exit, wrapper/child disagreement, absent/duplicate marker or later diagnostic is ERROR even if RSS is500000KiB (above the floor, below budget). Wrapper exit, measurement exit, marker count and peak are emitted together for evidence. A low peak still fails the existing floor rule.

## Deterministic gate regression

Command: `sh scripts/check/check-interp-worker-rss-budget.shs --selftest`.

Five numerical judge controls cover below/at/above budget and absent/below-floor peaks. Seven synthetic wrapper controls invoke the actual `check_worker -> measure_peak -> judge` production gate path, with a500000KiB receipt: expected exit/terminal positive control,139signal status, missing terminal, wrong exit0, wrapper2/child1 mismatch, duplicate terminal and trailing fatal diagnostic. Only the positive synthetic control passes. The optional wrapper path is an internal function argument used by selftest, not a production CLI/environment override.

Observed:12 gate fixtures PASS on the repair tree; shell syntax check PASS. No compiler, native worker, runtime build or real RSS measurement was executed. Synthetic positive controls test the gate, not production worker memory. Original Windows/Linux historical measurements remain historical; no new floor/performance claim is made.

Actual measurement still requires an independently admitted executable/source/runtime binding and canonical outer process-tree/resource containment. A trusted measurement wrapper and worker are assumed; textual output is not cryptographic executable attestation. Output after the expected terminal is intentionally rejected; provider format changes must be reviewed rather than silently accepted.
