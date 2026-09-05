# lint_string_utils_spec

> Purpose: Prove that is_ident_char.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lint_string_utils_spec

Purpose: Prove that is_ident_char.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/lint_string_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that is_ident_char.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### is_ident_char

#### accepts lowercase letters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts lowercase letters
- Verify: accepts lowercase letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts lowercase letters")
step("Verify: accepts lowercase letters")
# @req: REQ-COMPILER-LINT-001
expect(is_ident_char("a")).to_be_true()
expect(is_ident_char("z")).to_be_true()
```

</details>

#### accepts uppercase letters

- accepts uppercase letters
- Verify: accepts uppercase letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts uppercase letters")
step("Verify: accepts uppercase letters")
expect(is_ident_char("A")).to_be_true()
expect(is_ident_char("Z")).to_be_true()
```

</details>

#### accepts digits

- accepts digits
- Verify: accepts digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts digits")
step("Verify: accepts digits")
expect(is_ident_char("0")).to_be_true()
expect(is_ident_char("9")).to_be_true()
```

</details>

#### accepts underscore

- accepts underscore
- Verify: accepts underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts underscore")
step("Verify: accepts underscore")
expect(is_ident_char("_")).to_be_true()
```

</details>

#### rejects punctuation and whitespace

- rejects punctuation and whitespace
- Verify: rejects punctuation and whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects punctuation and whitespace")
step("Verify: rejects punctuation and whitespace")
expect(is_ident_char(".")).to_be_false()
expect(is_ident_char(" ")).to_be_false()
expect(is_ident_char("(")).to_be_false()
```

</details>

#### rejects multi-character input

- rejects multi-character input
- Verify: rejects multi-character input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects multi-character input")
step("Verify: rejects multi-character input")
expect(is_ident_char("ab")).to_be_false()
```

</details>

### find_substring

#### finds the first occurrence

- finds the first occurrence
- Verify: finds the first occurrence
   - Expected: find_substring("hello world", "world") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds the first occurrence")
step("Verify: finds the first occurrence")
expect(find_substring("hello world", "world")).to_equal(6)
```

</details>

#### returns -1 when not found

- returns -1 when not found
- Verify: returns -1 when not found
   - Expected: find_substring("hello", "xyz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns -1 when not found")
step("Verify: returns -1 when not found")
expect(find_substring("hello", "xyz")).to_equal(-1)
```

</details>

#### returns 0 for an empty needle

- returns 0 for an empty needle
- Verify: returns 0 for an empty needle
   - Expected: find_substring("hello", "") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns 0 for an empty needle")
step("Verify: returns 0 for an empty needle")
expect(find_substring("hello", "")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3725d86bcbbf208037ab4fb04ca1bab10224c4eb6a954818e310b590981a2a58`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3725d86bcbbf208037ab4fb04ca1bab10224c4eb6a954818e310b590981a2a58`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3725d86bcbbf208037ab4fb04ca1bab10224c4eb6a954818e310b590981a2a58`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/lint_string_utils_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/lint_string_utils_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/lint_string_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/lint_string_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/lint_string_utils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/lint_string_utils_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts lowercase letters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/lint_string_utils_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts uppercase letters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/lint_string_utils_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
