# JIT: "method lower not found on nil" during engine2d backend auto-resolution

**Date:** 2026-08-02 · **Severity:** medium · **Area:** Cranelift JIT method dispatch / engine2d backend resolve

## Symptom

Running a program that triggers engine2d `"auto"` backend resolution through
`bin/simple run` (Cranelift JIT engine) dies with
`method lower not found on nil` inside the resolution path. The same code is
correct under the tree-walk interpreter
(`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) and under
`bin/simple test` — the viable-probe resolver landed green there
(parity 17/17, resolver spec 6/6).

## Analysis

`.lower()` is dispatched on a value the JIT sees as nil at that point — an
engine-divergence defect in the JIT's method dispatch on a nullable/erased
receiver in the probe/rejection formatting path, not a defect in the
resolution logic itself (interpreter agrees with expected behavior). This is
another instance of the known run-vs-test engine divergence family
(`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`).

## Repro

Under JIT (`bin/simple run`, no execution-mode override), exercise
`detect_best_backend_viable()` /
`simple_web_resolved_engine2d_backend_name(w, h, "auto")` on a host where at
least one candidate backend is rejected. Interpreter mode is the workaround.

## Status

Open. Specs are unaffected (test lane = interpreter); the deployed JIT lane
should not be used for backend resolution until fixed.
