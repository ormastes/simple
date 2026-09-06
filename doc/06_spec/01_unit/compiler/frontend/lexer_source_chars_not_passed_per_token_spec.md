# lexer_source_chars_not_passed_per_token_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_source_chars_not_passed_per_token_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### lexer token-text compare does not pass source_chars by argument

#### has no free function taking the char array and uses the in-place method

- Verify: has no free function taking the char array and uses the in-place method


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: has no free function taking the char array and uses the in-place method")
val source = rt_file_read_text("src/compiler/10.frontend/core/lexer_struct.spl") ?? ""
expect(source.len() > 0).to_be_true()
expect(source).to_contain("fn chars_match(start: i64, end: i64, value: text) -> bool:")
expect(source).to_contain("self.chars_match(s, e, cached)")
expect(source).to_contain("self.chars_match(i, i + wlen, word)")
expect(source.contains("core_token_text_matches(self.source_chars")).to_be_false()
expect(source.contains("fn core_token_text_matches(chars: [text]")).to_be_false()
```

</details>

#### compares token spans correctly in place

- Verify: compares token spans correctly in place


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: compares token spans correctly in place")
# Fidelity: the in-place compare must accept exact spans and reject
# length and content mismatches, on the real lexer type.
val lx = make_core_lexer("fn main")
expect(lx.chars_match(0, 2, "fn")).to_be_true()
expect(lx.chars_match(3, 7, "main")).to_be_true()
expect(lx.chars_match(3, 7, "mail")).to_be_false()
expect(lx.chars_match(3, 6, "main")).to_be_false()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38c20b5b6dafafa2356f221a6b769f9a3fc5ae53ca910f1a0c8de895c73504b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38c20b5b6dafafa2356f221a6b769f9a3fc5ae53ca910f1a0c8de895c73504b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38c20b5b6dafafa2356f221a6b769f9a3fc5ae53ca910f1a0c8de895c73504b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no free function taking the char array and uses the in-place method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares token spans correctly in place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl. -->
