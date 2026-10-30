# CMM prefix range token versus repeated unary negation

Status: OPEN; grammar behavior requires a grounded repair and execution.

The historical expression system suite names `--1` as repeated unary negation
but previously asserted only a tautological diagnostic-count bound against a
local fake parser. The modernized suite uses the real production source parser
and retains the original positive requirement: no errors and Neg(Neg(PlainInt)).
Do not claim it passes without executing that real assertion.

Static production analysis: the lexer emits RangeTo for `--`; parse_unary
handles Minus but not RangeTo, and range parsing expects a left primary.
Thus preserving the original source input is a likely real regression rather
than justification to rename it a successful negative test. No language-domain
equivalence or compatibility is established by the old placeholder suite.

Removal requires a justified lexical/grammar decision that preserves binary
range semantics and executes both this positive repeated-negation case and
range boundary/operand regressions through the actual parser. Keep unsupported
behavior explicit; do not silently replace compact grammar with a workaround.
