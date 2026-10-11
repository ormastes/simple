# TUI-web Phase 1 rendering and mutation failures

Status: Unicode repair verified by 4/4 focused Phase1 seed regressions.
Lifecycle and event-queue failures remain open; no workaround was applied.

## Producer-bound observation

The first diagnostic execution of
`test/03_system/gui/ui/tui_web_render_spec.spl` declared/executed 3 scenarios,
with 0 passed and 3 failed. Evidence:
`build/phase-one-ui-diagnostic/tui_web_render_spec/cycle-one.log`.
The logged child is the admitted Phase 1 seed at
`/tmp/beta-qual-4159b0b6/src/compiler_rust/target/bootstrap.generations/42089cdfb4fbaa7e93dea90362f7a1476568aa4c36a792c90f68c8eea693934c-cdd98df087f336ba0135ebdc01888808b920d03545627b964d1d5215cf644b57/simple`.
This evidence is specific to that producer, not a self-hosted runtime pass.

## Confirmed Unicode owner defect

Observed error: `string index out of bounds: index is 1 but length is 1
(preview="┌")`.

`src/app/ui.tui_web/screen_to_html.spl` escaped each character using
`while i < input.len(): input[i]`. In this producer, length counts UTF-8 bytes
while bracket indexing uses codepoints. A box corner occupies three bytes but
one codepoint; the second access fails. The outer converter repeated the same
mismatch with `rendered.len()` and `rendered[i]`, so fixing only the escaping
helper would leave another failure.

The source repair iterates `input.split("")` for escaping and splits the ANSI
input once before using array indexes and array length for the converter.
This follows the existing codepoint iteration in `app.ui.tui.screen._to_chars`.
Boundary empty entries emitted by splitting are harmless empty text; ANSI
lookahead advances within the same array. Numeric ANSI parameter parsing is
unchanged because the converter only admits ASCII digits and semicolons there.

Focused regression: `test/01_unit/app/ui/tui_web_unicode_spec.spl` covers the
single corner, mixed scripts/emoji/combining characters, HTML metacharacters,
ANSI style boundaries, empty input and truncated escape sequences. Its manual
is `doc/06_spec/01_unit/app/ui/tui_web_unicode_spec.md`. Its cycle-one log
records 4/4 PASS. The system cycle-two log records 1/3 PASS: the rendering
scenario now succeeds while lifecycle and queue reuse still fail. Both guards
report quiescent child trees. Exact source and producer hashes are retained in
`build/phase-one-ui-diagnostic/unicode-repair-inputs.json`. These are Phase1
seed results, not native/release qualification.

## Open lifecycle expression mutation failure

The unchanged system scenario evaluates `match backend.init():` and checks
`backend.initialized` afterward. The observed failure is `expected false to
equal true`. The owner method sets `self.initialized = true` then returns
`Ok(true)`. Source inspection gives no intended branch that leaves it false.

A lost receiver update in a result-bearing expression is suspected, not proven.
The inspected producer source has a self-writeback path in
`src/compiler_rust/compiler/src/interpreter/expr/calls.rs`, and its match
statement evaluates the subject through the mutable environment evaluator.
Consequently a missing generic match writeback path cannot be asserted merely
from this symptom. The exact compiled producer and its receiver/return/closure
scope behavior require a minimal diagnostic before assigning compiler ownership.
The pure-Simple evaluator likewise evaluates the match scrutinee before
entering arm scope (`compiler/10.frontend/core/interpreter/eval_stmts.spl`).

## Open event-queue reuse failure

The unchanged system scenario enqueues Enter and an action, polls both in
match statements, checks exhaustion, then enqueues Escape. It reports
`Expected the newly queued Escape key` on the final match. Production
`poll_event` advances its head and resets queue/head at exhaustion; the source
contract supports reuse. The output does not identify the unexpected variant
or prove exactly which mutation was lost.

Next diagnostic should compare standalone, bound-result, and match-subject
calls on a minimal local mutable class, retaining exact return values and
receiver fields after each call. Then inspect the real queue's head, length,
and returned variant at each step on the same producer. Do not remove the
compact match syntax, weaken the system assertions, or report a passing
long-form rewrite as a compiler fix. A producer defect needs a repaired build
and producer-specific regression evidence; source changes alone cannot repair
an already-built seed binary.
