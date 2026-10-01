# primitive_api_lint_spec

> Purpose: This spec proves primitive_api lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_api_lint_spec

Purpose: This spec proves primitive_api lint.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/primitive_api_lint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves primitive_api lint.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### primitive_api lint

#### flags bare primitive public function parameter and return types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags bare primitive public function parameter and return types
   - Expected: count_visible_primitive_api(source) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PRIMITIVEAPILINT-001
step("flags bare primitive public function parameter and return types")
val source =
    "pub fn bad(x: i64) -> i64:\n" +
    "    return x\n"

expect(count_visible_primitive_api(source)).to_equal(2)
```

</details>

#### does not flag newunit semantic wrapper public APIs

- does not flag newunit semantic wrapper public APIs
- does not flag newunit semantic wrapper public APIs
   - Expected: count_visible_primitive_api(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not flag newunit semantic wrapper public APIs")
step("does not flag newunit semantic wrapper public APIs")
val source =
    "newunit UserId: i64 as uid\n" +
    "\n" +
    "pub fn current_user() -> UserId:\n" +
    "    return 42_uid\n"

expect(count_visible_primitive_api(source)).to_equal(0)
```

</details>

#### audits bool and text public primitives without changing lint count

- audits bool and text public primitives without changing lint count
- audits bool and text public primitives without changing lint count
   - Expected: count_visible_primitive_api(source) equals `0`
   - Expected: entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("audits bool and text public primitives without changing lint count")
step("audits bool and text public primitives without changing lint count")
val source =
    "pub fn enabled(name: text) -> bool:\n" +
    "    return name.len() > 0\n"

val entries = primitive_api_audit_source(source, "sample.spl")
val report = primitive_api_audit_report(source, "sample.spl")
expect(count_visible_primitive_api(source)).to_equal(0)
expect(entries.len()).to_equal(2)
expect(report).to_contain("needs_domain_text_type")
expect(report).to_contain("needs_bool_wrapper_or_enum")
```

</details>

#### does not flag pure math signatures

- does not flag pure math signatures
- does not flag pure math signatures
   - Expected: count_visible_primitive_api(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not flag pure math signatures")
step("does not flag pure math signatures")
val source =
    "pub fn add(left: i64, right: i64) -> i64:\n" +
    "    return left + right\n"

expect(count_visible_primitive_api(source)).to_equal(0)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-PRIMITIVEAPILINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b7922ac4ccb79b0b271864122512665bb0e8d2503ba69c48058c624c6053040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b7922ac4ccb79b0b271864122512665bb0e8d2503ba69c48058c624c6053040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b7922ac4ccb79b0b271864122512665bb0e8d2503ba69c48058c624c6053040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/primitive_api_lint_spec.spl
mirror: doc/06_spec/integration/app/primitive_api_lint_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/primitive_api_lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/primitive_api_lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/primitive_api_lint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/primitive_api_lint_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags bare primitive public function parameter and return types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/primitive_api_lint_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag newunit semantic wrapper public APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/primitive_api_lint_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'audits bool and text public primitives without changing lint count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
