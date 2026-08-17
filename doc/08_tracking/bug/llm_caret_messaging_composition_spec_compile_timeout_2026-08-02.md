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

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: the "does not finish compiling within the test budget" claim is
implausible at this files size — treat as stale pending re-measure.**

`test/01_unit/app/llm_caret/messaging/composition_spec.spl` is **134 lines with
5 declarations**. Against the measured cost table in `.claude/rules/commands.md`
that is a small file by every axis that actually drives cost: the pathological
case there (`src/compiler/50.mir/hwir/zca_rows.spl`) is 1,901 lines / 30
complex declarations, and even a 45-declaration / 315-line fixture completed.
Declaration count scales linearly and content complexity is the real driver;
nothing about a 134-line / 5-declaration spec predicts a budget overrun.

The original evidence also predates the two known false-timeout sources named
in the session brief (`SIMPLE_TIMEOUT_SECONDS` discarded until `a034851236d`;
the mis-thresholded `kill_simple_monitor.shs`).

**Not re-measured to a `Results:` line from this lane** (host load average
81-133; UNVERIFIED per the briefs rc=143 rule). Re-run with an explicit
`--timeout` on a quiet host; expect it to pass.
