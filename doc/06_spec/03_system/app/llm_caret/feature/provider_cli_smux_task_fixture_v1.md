# Actual smux constrained-execution replay fixture

Status: AUTHORED_NOT_RUN; real admitted/native invocation is NOT_COVERED.

The real harness must supply the actual V5 owner already retaining the exact
signed Host execute request, copied restriction, and its actual prior response/
error. Do not substitute a constructed owner, fake grant or scripted CLI output.

Invoke `check_real_smux_retained_constraint_replay_v1`. Exact replay must preserve
the original response/continuation. Changed workdir under the same signed request
must return `runtime-host-execution-constraint-changed`. Replaying via legacy nil
also refuses a previously Some-bound execution. Retrying the original complete
restriction then returns the original result, showing refusal retained the owner.
Run with actual pending and actual completed retained executions; neither was run
while authoring this fixture. Keep returned owner and charge through real cleanup.

Additional native variants remain NOT_RUN: changing every other restriction field,
caller array mutation after begin, queued/unknown controlled input, exact frame/
attempt replay, partial prefix and explicit known suffix, stale attachment, issuer
revocation, and close while a native receipt is pending. Existing V5 implements
these input protocols; app delegates them without a second queue or automatic
retry. Native write completion proves no provider consumption or stdin EOF.
