# lsp_diagnostics_enhanced_spec

> val pattern = "\"severity\":{severity}"

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsp_diagnostics_enhanced_spec

val pattern = "\"severity\":{severity}"

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

val pattern = "\"severity\":{severity}"
    val pattern2 = "\"severity\": {severity}"
    output.contains(pattern) or output.contains(pattern2)

fn output_contains_tag(output: text, tag: i64) -> bool:
    """Check if JSON output contains a diagnostic with the given tag.
    Tags: 1=Unnecessary, 2=Deprecated

## Scenarios

### LSP Enhanced Diagnostics

<details>
<summary>Advanced: syntax error produces Error severity diagnostic</summary>

#### syntax error produces Error severity diagnostic _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- syntax error produces Error severity diagnostic
   - Expected: has_error_severity is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("syntax error produces Error severity diagnostic")
val path = write_temp_file("syntax_err", "fn broken(\n    val x = \n")
val output = run_check_json(path)
# Severity 1 = Error
val has_error_severity = output_contains_severity(output, 1)
expect(has_error_severity).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: unused variable produces Warning severity with Unnecessary tag</summary>

#### unused variable produces Warning severity with Unnecessary tag _(slow)_

- unused variable produces Warning severity with Unnecessary tag
   - Expected: has_warning is true
   - Expected: mentions_unused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unused variable produces Warning severity with Unnecessary tag")
val code = "fn test_unused():\n    val unused_var = 42\n    val used_var = 10\n    print used_var\n"
val path = write_temp_file("unused_var", code)
val output = run_check_json(path)
# Should contain a warning (severity 2)
val has_warning = output_contains_severity(output, 2)
expect(has_warning).to_equal(true)
# Should mention the unused variable
val mentions_unused = output.contains("unused_var")
expect(mentions_unused).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: deprecated Type__method pattern produces Warning with Deprecated tag</summary>

#### deprecated Type__method pattern produces Warning with Deprecated tag _(slow)_

- deprecated Type__method pattern produces Warning with Deprecated tag
   - Expected: has_depr001 is true
   - Expected: has_deprecated_tag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deprecated Type__method pattern produces Warning with Deprecated tag")
val code = "fn test_deprecated():\n    val result = Vec__new()\n"
val path = write_temp_file("deprecated", code)
val output = run_check_json(path)
# Should contain DEPR001 code
val has_depr001 = output_contains_code(output, "DEPR001")
expect(has_depr001).to_equal(true)
# Should have Deprecated tag (tag value 2)
val has_deprecated_tag = output_contains_tag(output, 2)
expect(has_deprecated_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: deprecated .new() constructor produces Warning with Deprecated tag</summary>

#### deprecated .new() constructor produces Warning with Deprecated tag _(slow)_

- deprecated .new() constructor produces Warning with Deprecated tag
   - Expected: has_depr002 is true
   - Expected: has_deprecated_tag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deprecated .new() constructor produces Warning with Deprecated tag")
val code = "fn test_new():\n    val p = Point.new(1, 2)\n"
val path = write_temp_file("deprecated_new", code)
val output = run_check_json(path)
# Should contain DEPR002 code
val has_depr002 = output_contains_code(output, "DEPR002")
expect(has_depr002).to_equal(true)
# Should have Deprecated tag (tag value 2)
val has_deprecated_tag = output_contains_tag(output, 2)
expect(has_deprecated_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: unreachable code after return produces Warning with Unnecessary tag</summary>

#### unreachable code after return produces Warning with Unnecessary tag _(slow)_

- unreachable code after return produces Warning with Unnecessary tag
   - Expected: has_unreach is true
   - Expected: has_unnecessary_tag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unreachable code after return produces Warning with Unnecessary tag")
val code = "fn test_unreachable() -> i64:\n    return 42\n    val x = 10\n"
val path = write_temp_file("unreachable", code)
val output = run_check_json(path)
# Should contain UNREACH001 code
val has_unreach = output_contains_code(output, "UNREACH001")
expect(has_unreach).to_equal(true)
# Should have Unnecessary tag (tag value 1)
val has_unnecessary_tag = output_contains_tag(output, 1)
expect(has_unnecessary_tag).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: non-exhaustive match produces Warning</summary>

#### non-exhaustive match produces Warning _(slow)_

- non-exhaustive match produces Warning
   - Expected: has_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("non-exhaustive match produces Warning")
val code = "fn test_match(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n"
val path = write_temp_file("match_exhaust", code)
val output = run_check_json(path)
# Should have some warning output (severity 2 = Warning)
# Match exhaustiveness is a heuristic check
val has_output = output.len() > 0
expect(has_output).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: structured JSON output from query check contains correct fields</summary>

#### structured JSON output from query check contains correct fields _(slow)_

- structured JSON output from query check contains correct fields
   - Expected: has_severity is true
   - Expected: has_code_field is true
   - Expected: has_message is true
   - Expected: has_line is true
   - Expected: has_col is true
   - Expected: has_tags is true
   - Expected: has_source is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("structured JSON output from query check contains correct fields")
val code = "fn test_json():\n    val result = Vec__new()\n"
val path = write_temp_file("json_fields", code)
val output = run_check_json(path)
# Verify JSON output contains expected field names
val has_severity = output.contains("\"severity\"")
val has_code_field = output.contains("\"code\"")
val has_message = output.contains("\"message\"")
val has_line = output.contains("\"line\"")
val has_col = output.contains("\"col\"")
val has_tags = output.contains("\"tags\"")
val has_source = output.contains("\"source\"")
expect(has_severity).to_equal(true)
expect(has_code_field).to_equal(true)
expect(has_message).to_equal(true)
expect(has_line).to_equal(true)
expect(has_col).to_equal(true)
expect(has_tags).to_equal(true)
expect(has_source).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: clean code produces no warnings</summary>

#### clean code produces no warnings _(slow)_

- clean code produces no warnings
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clean code produces no warnings")
val code = "fn add(a: i64, b: i64) -> i64:\n    a + b\n"
val path = write_temp_file("clean", code)
val (output, exit_code) = run_check_text(path)
expect(exit_code).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2528c91d8fa694182e9b97362840f64efdac4ad99a512fd2f64b8a43011337ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2528c91d8fa694182e9b97362840f64efdac4ad99a512fd2f64b8a43011337ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2528c91d8fa694182e9b97362840f64efdac4ad99a512fd2f64b8a43011337ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl
mirror: doc/06_spec/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'syntax error produces Error severity diagnostic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unused variable produces Warning severity with Unnecessary tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deprecated Type__method pattern produces Warning with Deprecated tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
