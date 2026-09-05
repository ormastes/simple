# Self-hosted lexer: multiline `if` condition continued with a leading `and`

> A boolean `if` condition split across two lines, with the operator at the START of the continuation line, must be ONE condition in the self-hosted frontend:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Self-hosted lexer: multiline `if` condition continued with a leading `and`

A boolean `if` condition split across two lines, with the operator at the START of the continuation line, must be ONE condition in the self-hosted frontend:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / Stage-2 self-host parity |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A boolean `if` condition split across two lines, with the operator at the START
of the continuation line, must be ONE condition in the self-hosted frontend:

```simple
if declaration.function_symbol_id == function_symbol_id
    and declaration.base_local_id == base_local_id:
    ...
```

The Stage-2 self-hosted parser was reported to terminate the condition after the
first operand and fail at the newline with `expected :, got Newline`, while the
Rust seed accepted the same text. Bootstrap sources carried explicit parentheses
as a workaround.

## Why this spec drives the LEXER, not the language

`test/01_unit/compiler/parser_leading_operator_continuation_spec.spl` already
covers the leading-operator family, but a `.spl` spec's own source is lexed by
whatever binary EXECUTES the spec — that is the Rust seed, which never had this
defect. It therefore cannot say anything about the self-hosted frontend.

This spec instead drives the pure-Simple scanner directly
(`core.lexer.lex_init`/`lex_next`, i.e. `src/compiler/10.frontend/core/
lexer_struct.spl`) over source held in a string. The oracle is absolute: the
continuation is glued exactly when NO `Newline` token (kind 180) is emitted
between the last token of the first line and the leading `and` (kind 55).

The glue is produced by `CoreLexer.leading_op_continues`, whose three guards are
each covered below — the two negative controls matter as much as the positive
case, because folding either shape into the previous line silently miscompiles
working code.

## Token kinds used

`6` Ident · `40` if · `55` and · `161` Colon · `180` Newline · `181` Indent ·
`182` Dedent · `190` EOF.

## Scenarios

### self-hosted lexer glues a leading `and` onto an `if` condition

#### emits no Newline between the condition operand and the leading `and`

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits no Newline between the condition operand and the leading `and`
- Scan the two-line `if` condition through the pure-Simple lexer
- Locate the `if` keyword and the leading `and` in the token stream
- Assert the condition was never terminated at the newline
   - Expected: newlines_between(kinds, if_at, and_at) equals `0`
- Assert the token immediately before `and` is the first operand
   - Expected: kinds[and_at - 1] equals `KIND_IDENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits no Newline between the condition operand and the leading `and`")
step("Scan the two-line `if` condition through the pure-Simple lexer")
val kinds = kinds_of(REPRO_IF)

step("Locate the `if` keyword and the leading `and` in the token stream")
val if_at = index_of_kind(kinds, KIND_IF)
val and_at = index_of_kind(kinds, KIND_AND)
expect(if_at).to_be_greater_than(-1)
expect(and_at).to_be_greater_than(if_at)

step("Assert the condition was never terminated at the newline")
# This is the whole defect: a Newline here is the `expected :, got
# Newline` the Stage-2 parser reported.
expect(newlines_between(kinds, if_at, and_at)).to_equal(0)

step("Assert the token immediately before `and` is the first operand")
expect(kinds[and_at - 1]).to_equal(KIND_IDENT)
```

</details>

#### keeps a block body that starts with a unary minus out of the header

- keeps a block body that starts with a unary minus out of the header
- Scan an `if c:` header whose body begins with `-1`
- Assert the header is still terminated by a Newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a block body that starts with a unary minus out of the header")
step("Scan an `if c:` header whose body begins with `-1`")
val kinds = kinds_of(CONTROL_BLOCK_BODY)

step("Assert the header is still terminated by a Newline")
# Guard 1 (`token_can_end_expr`): the previous token is a Colon, which
# cannot end an expression, so the `-1` line must NOT be glued on.
val if_at = index_of_kind(kinds, KIND_IF)
expect(if_at).to_be_greater_than(-1)
expect(newlines_between(kinds, if_at, kinds.len())).to_be_greater_than(0)
```

</details>

#### does not glue a following line written at the same indent

- does not glue a following line written at the same indent
- Scan a statement followed by a same-column line
- Assert the statement is terminated rather than continued


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not glue a following line written at the same indent")
step("Scan a statement followed by a same-column line")
val kinds = kinds_of(CONTROL_SAME_INDENT)

step("Assert the statement is terminated rather than continued")
# Guard 2 (strictly-deeper indent): this is the implicit-return shape
# live in src/runtime/simple_core/core_string.spl. Gluing it would
# silently miscompile working code.
expect(newlines_between(kinds, 0, kinds.len())).to_be_greater_than(2)
```

</details>

#### reaches EOF rather than stalling on the continued condition

- reaches EOF rather than stalling on the continued condition
- Scan the reproducer to completion
- Assert the stream terminated with a real EOF token
   - Expected: kinds[kinds.len() - 1] equals `KIND_EOF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reaches EOF rather than stalling on the continued condition")
step("Scan the reproducer to completion")
val kinds = kinds_of(REPRO_IF)

step("Assert the stream terminated with a real EOF token")
# A dead lexer returns kind 0 forever; the cap in kinds_of() would then
# hand back 200 tokens with no EOF.
expect(kinds[kinds.len() - 1]).to_equal(KIND_EOF)
expect(kinds.len()).to_be_less_than(200)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f97654008dde5708085ca3aee9ed47230c942ab740c43fe178a3f9b435e53e78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f97654008dde5708085ca3aee9ed47230c942ab740c43fe178a3f9b435e53e78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f97654008dde5708085ca3aee9ed47230c942ab740c43fe178a3f9b435e53e78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no Newline between the condition operand and the leading `and`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a block body that starts with a unary minus out of the header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not glue a following line written at the same indent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
