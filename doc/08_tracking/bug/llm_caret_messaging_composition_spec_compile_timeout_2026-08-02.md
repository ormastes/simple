# LLM Caret Messaging Composition Spec Compile Timeout

Date: 2026-08-02
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom

The focused command below emits compiler and runtime-family warnings but never
reaches test execution or a test summary before the 120-second watchdog exits
with code 124:

```sh
bin/simple test test/01_unit/app/llm_caret/messaging/composition_spec.spl \
  --mode=interpreter
```

## Scope

The regression appeared after the composition closure added canonical
message-to-task routing, context-manifest creation, agent-session injection,
and consumed receipts. Focused source/diff checks do not report a diagnostic,
but they also do not establish runtime correctness.

The broader primitive HTTP application SSpec, which exercises the same routing
path through real request dispatch and PureDatabase, completes with exit code
0. The remaining defect is therefore isolated to this composition-spec compile
closure rather than being evidence of a routing assertion failure.

## Required fix/evidence

- Identify the compilation phase responsible for the stall.
- Keep the full composition behavior; do not remove routing to shrink closure.
- Produce a terminal SSpec summary within the repository's 120-second bound.
- Record warm compilation and execution timing separately.
