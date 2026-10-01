# lexer_indentation_eof_emits_token_spec

> Purpose: Prove that handle_indentation never leaves the token stream dead at EOF.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_indentation_eof_emits_token_spec

Purpose: Prove that handle_indentation never leaves the token stream dead at EOF.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that handle_indentation never leaves the token stream dead at EOF.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### handle_indentation never leaves the token stream dead at EOF

#### emits EOF (not the constructor default 0) for a whitespace-only source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits EOF (not the constructor default 0) for a whitespace-only source
- Verify: emits EOF (not the constructor default 0) for a whitespace-only source
   - Expected: first_kind_of("   ") equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits EOF (not the constructor default 0) for a whitespace-only source")
step("Verify: emits EOF (not the constructor default 0) for a whitespace-only source")
# @req: REQ-COMPILER-FRONTEND-001
# The minimal trigger. `at_end()` is false at pos 0 (three chars of
# source), so scan_token() dispatches to handle_indentation(), which
# consumes all three spaces and then hit the bare `return`.
expect(first_kind_of("   ")).to_equal(190)
```

</details>

#### emits EOF for a tab-only source

- emits EOF for a tab-only source
- Verify: emits EOF for a tab-only source
   - Expected: first_kind_of("\t\t") equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits EOF for a tab-only source")
step("Verify: emits EOF for a tab-only source")
expect(first_kind_of("\t\t")).to_equal(190)
```

</details>

#### emits EOF for a genuinely empty source

- emits EOF for a genuinely empty source
- Verify: emits EOF for a genuinely empty source
   - Expected: first_kind_of("") equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits EOF for a genuinely empty source")
step("Verify: emits EOF for a genuinely empty source")
# Control: this took scan_token()'s own at_end() branch and was already
# correct. It must stay correct.
expect(first_kind_of("")).to_equal(190)
```

</details>

#### never yields kind 0, the impossible token kind, on any of these

- never yields kind 0, the impossible token kind, on any of these
- Verify: never yields kind 0, the impossible token kind, on any of these


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never yields kind 0, the impossible token kind, on any of these")
step("Verify: never yields kind 0, the impossible token kind, on any of these")
expect(first_kind_of("   ")).to_not_equal(0)
expect(first_kind_of("\t\t")).to_not_equal(0)
expect(first_kind_of(" \t ")).to_not_equal(0)
```

</details>

#### still reaches EOF on a normal program whose last line is blank-ish

- still reaches EOF on a normal program whose last line is blank-ish
- Verify: still reaches EOF on a normal program whose last line is blank-ish
   - Expected: kinds.len() > 1 is true
   - Expected: kinds[kinds.len() - 1] equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reaches EOF on a normal program whose last line is blank-ish")
step("Verify: still reaches EOF on a normal program whose last line is blank-ish")
# Trailing indentation with no newline after it is the same shape as the
# trigger, reached mid-file instead of at pos 0.
val kinds = kinds_until_eof("fn main():\n    print(1)\n   ", 40)
expect(kinds.len() > 1).to_equal(true)
expect(kinds[kinds.len() - 1]).to_equal(190)  # oracle: 190 — named expected value from the requirement
```

</details>

#### still reaches EOF on an ordinary well-formed program

- still reaches EOF on an ordinary well-formed program
- Verify: still reaches EOF on an ordinary well-formed program
   - Expected: kinds[kinds.len() - 1] equals `190`
   - Expected: kinds.len() > 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reaches EOF on an ordinary well-formed program")
step("Verify: still reaches EOF on an ordinary well-formed program")
# Non-vacuity control: the fix must not have shortened a healthy stream.
val kinds = kinds_until_eof("fn main():\n    print(1)\n", 40)
expect(kinds[kinds.len() - 1]).to_equal(190)  # oracle: 190 — named expected value from the requirement
expect(kinds.len() > 5).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-FRONTEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99e0243a676887a5df07f1d8da059c1d08b0d2487fffd3b17b921ffceddb548a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99e0243a676887a5df07f1d8da059c1d08b0d2487fffd3b17b921ffceddb548a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99e0243a676887a5df07f1d8da059c1d08b0d2487fffd3b17b921ffceddb548a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits EOF (not the constructor default 0) for a whitespace-only source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits EOF for a tab-only source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits EOF for a genuinely empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
