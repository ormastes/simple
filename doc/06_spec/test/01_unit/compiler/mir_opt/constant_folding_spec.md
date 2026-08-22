# MIR ConstantFolding Skeleton Specification

Constant folding remains requested in compatibility pipeline descriptions but
is excluded from effective pipelines because its pass status is `Skeleton`.

| Contract | Evidence |
|---|---|
| Pipeline truth | Requested plans may name the pass; effective plans do not. |
| Direct-call safety | `fold_block`, instruction, terminator, function, and wrapper entrypoints return their inputs unchanged. |
| Honest statistics | New pass objects report zero folded instructions and branches. |
| No dormant rewrite | Host arithmetic, algebraic identity rewriting, and branch replacement bodies are absent. |

Rehabilitation requires a shared typed evaluator accepting operand types and
returning a typed result or explicit rejection. It must implement exact target
width/signedness, language overflow and trap behavior, division/remainder and
shift legality, F32/F64 rounding/NaN/signed-zero behavior, result-type checks,
and no-change storage reuse. Positive and negative witnesses, exact receipts,
post-pass verification, idempotence, and semantic differential execution are
mandatory before `Active` status.

Source: `test/01_unit/compiler/mir_opt/constant_folding_spec.spl`.
