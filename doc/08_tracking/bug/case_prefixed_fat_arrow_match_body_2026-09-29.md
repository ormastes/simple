# Case-prefixed fat-arrow match bodies

## Reproduction and cause

Frozen668 Linux Phase2 full CLI diagnostic attempt3 failed to parse
`src/app/ui.render/_TuiWidgets/core_widgets.spl:93` and
`extended_widgets.spl:142`: `case _ => return ...` produced `expected :, got =>`.
The case-prefixed match branch required a colon. Its caseless fat-arrow branch
also parsed same-line bodies only as expressions, losing statement semantics.

## Selected correction

Both fat-arrow spellings consume the separator and use the existing block parser,
which supports an inline expression, inline statement or indented block. Colon
and thin-arrow handling remain covered. Arm guard, binding and rationale storage
are unchanged. No AST tags, token IDs or runtime ABI change is required.

The grammar accepts wildcard syntax so the diagnostic policy can analyze it.
This does not endorse bare wildcards in owned compiler code: a regression verifies
that the existing `REQC004` warning survives for a bare text wildcard, while
explicit rationale metadata is preserved. Actual native-build warning routing
and the two UI fallback policies are separate corrections; do not silently move
catch-all behavior into an unreported fallthrough.

## Verification

`test/01_unit/compiler/frontend/match_case_fat_arrow_spec.spl` asserts AST body
tags, exact return values, complete block lengths, alternative guards, REQC004,
rationale preservation, existing separators and malformed-body rejection.
Bootstrap-only source-built parser evidence passed across two bounded cycles:
cases1–4 on d405819f00df98f51320631f8001550ba5852e89, then corrected case5 and
previously unrun cases6–9 on77edb2042354935ded483e015a4422263949445d. Production
parser bytes are identical between those commits. Each component build linked
87 modules; cycle2 exited0 with exact expected stdout, unchanged input pins and
empty owned-process cleanup. RSS monitoring did not enforce a memory cap.

The original pipe-alternative case5 failed and remains an open separate bug:
`match_pipe_alternative_consumed_as_bitwise_or_2026-09-29.md`. The corrected
case uses comma-separated alternatives to isolate guard/body preservation.
Passing cases1–4 were not rerun. No original-suite, full CLI, native producer,
interpreter-wide, MCP/LSP or bootstrap qualification is claimed. The old product
batch was not rerun.
