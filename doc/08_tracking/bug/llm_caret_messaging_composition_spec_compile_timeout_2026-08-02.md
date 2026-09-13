# LLM Caret Messaging Composition Spec Compile Timeout

Date: 2026-08-02
Status: Open

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

## Re-check 2026-09-13

Not reproducible. `bin/simple test test/01_unit/app/llm_caret/messaging/composition_spec.spl --mode=interpreter --no-session-daemon` on the deployed seed completes in 14947ms (well under the 120s watchdog), `5 total, 5 passed, 0 failed`.

- Status: CLOSED (2026-09-13) — not reproducible on `bin/release/aarch64-unknown-linux-gnu/simple` (hand-linked from `/home/yoon/dev/simple`, 2026-09-13)
