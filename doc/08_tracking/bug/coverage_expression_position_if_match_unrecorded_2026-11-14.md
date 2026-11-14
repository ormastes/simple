# Coverage: `if` / `match` in expression position is counted but never recorded (2026-11-14)

**Status:** OPEN. **Area:** seed coverage collector
(`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`, `record_node_coverage`,
called from `block_exec.rs:336` and `node_exec.rs:435`) versus the module report's
denominator (`src/lib/common/coverage_module_report.spl`, `_cov_is_recordable`).

## Symptom

`spl-coverage module` cannot report 90% lines for a module written in the tail-`match`
style, however completely it is tested. `_cov_is_recordable` counts every line that starts
with `if ` or `match ` as executable ("Statement kinds the collector records"), but the
collector, as measured, records a line only when the node runs as a STATEMENT. An `if` / `match` /
`if val` that is evaluated for its value is not recorded:

- the last expression of a function body (`fn f(k): match k: ...`),
- the last expression of a match arm, and anything that is last inside that.

Statements inside such a block are recorded normally, so the header shows as missed while
lines under it show as hit.

## Evidence

Probe module (seed `simple-dynlib-20261113`, interpreter, `SIMPLE_COVERAGE=1`): a function
whose body is `match k:` with a nested arm-tail `match v:`, and one whose body is
`if x > 0: ... else: ...`, were each called on both paths. The header lines were not in the
artifact; `case 1: return true` under them and a non-tail `match` in a sibling function were.

`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl` at this change:
231 executable lines, 190 hit, 41 missed, and all 41 are such headers
(34 `match`, 7 `if` / `if val`): lines 29, 32, 36, 44, 61, 63, 67, 90, 92, 97, 102, 107, 112, 124, 135, 157, 164, 166, 172, 176, 180, 184, 257, 297, 300, 315, 353, 362, 415, 421, 455, 469, 472, 513, 514, 524, 550, 576, 598, 600, 610.
39 of them have a recorded hit inside their own block. Lines 44 and 610 have only bare
calls under them (not recordable); their execution is shown by assertions on the result
(`enum_payload_type_evidence_spec.spl`, alias compatibility; `enum_payload_local_evidence_spec.spl`,
`is_runtime_value_local` after an enum slot decode).

So the reported 82.2% is 190 of 190 lines the collector is able to record.

## Fix options (not done here)

1. Collector: record the node when an `if` / `match` is evaluated as an expression too.
   This is the faithful fix; it needs a seed rebuild.
2. Report: drop expression-position headers from the denominator. Pure Simple, no rebuild,
   but it changes every module's figure and needs block-structure analysis in a text
   classifier. Owner decision.
3. Not recommended: rewriting production modules so every header is a statement.

Also seen while probing, not investigated: a function `val keep = 1` / `if val y = x:`
(whose body ends `case _: ()`) / `keep` returned `()` instead of `1` on the seed
interpreter for a present `x` that took the wildcard arm.
