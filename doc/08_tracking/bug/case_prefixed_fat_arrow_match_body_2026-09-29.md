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
Execution evidence is pending. The old product batch is not rerun.
