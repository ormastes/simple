# Eprint Builtin Native Path Specification

> Tests covering eprint builtin resolves on the native HIR path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Eprint Builtin Native Path Specification

## Scenarios

### eprint builtin resolves on the native HIR path

#### keeps the native runtime provider independent of the legacy spl provider

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the native runtime provider independent of the legacy spl provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the native runtime provider independent of the legacy spl provider")
val runtime_source = rt_file_read_text("src/runtime/runtime_native.c") ?? ""

expect(runtime_source).to_contain("void rt_eprintln(const char* s)")
expect(runtime_source).to_contain("if (s) fputs(s, stderr);")
expect(runtime_source).to_contain("fputc('\\n', stderr);")
expect(runtime_source).to_not_contain("spl_eprintln(s);")
```

</details>

#### lowers a module calling eprint with zero diagnostics

- lowers a module calling eprint with zero diagnostics
   - Expected: unresolved_eprint is false
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a module calling eprint with zero diagnostics")
val src = "fn warn(path: text):\n" +
    "    eprint(\"[lexer_fatal] empty source handed to lexer\")\n"
val errors = lower_single(src, "testdata/eprint_builtin.spl", "testdata.eprint_builtin")
var unresolved_eprint = false
for m in errors:
    if m.contains("unresolved name: eprint"):
        unresolved_eprint = true
expect(unresolved_eprint).to_equal(false)
expect(errors.len()).to_equal(0)
```

</details>

#### treats eprint like print: both lower with zero errors side by side

- treats eprint like print: both lower with zero errors side by side
   - Expected: unresolved_names equals `0`
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats eprint like print: both lower with zero errors side by side")
val src = "fn both(msg: text):\n" +
    "    print(msg)\n" +
    "    eprint(msg)\n"
val errors = lower_single(src, "testdata/eprint_vs_print.spl", "testdata.eprint_vs_print")
var unresolved_names = 0
for m in errors:
    if m.contains("unresolved name:"):
        unresolved_names = unresolved_names + 1
expect(unresolved_names).to_equal(0)
expect(errors.len()).to_equal(0)
```

</details>

#### control: an unrelated unknown callee still errors loudly

- control: an unrelated unknown callee still errors loudly
   - Expected: unresolved_names equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("control: an unrelated unknown callee still errors loudly")
val src = "fn bad(msg: text):\n" +
    "    definitely_not_a_builtin(msg)\n"
val errors = lower_single(src, "testdata/eprint_control.spl", "testdata.eprint_control")
var unresolved_names = 0
for m in errors:
    if m.contains("unresolved name: definitely_not_a_builtin"):
        unresolved_names = unresolved_names + 1
expect(unresolved_names).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering eprint builtin resolves on the native HIR path.
- eprint builtin resolves on the native HIR path

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

- Canonical SPipe generation for source `0aeaba42d5322175bd8d900adcb6ab79341f3511d44a8672b0b9cf8892826afc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0aeaba42d5322175bd8d900adcb6ab79341f3511d44a8672b0b9cf8892826afc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0aeaba42d5322175bd8d900adcb6ab79341f3511d44a8672b0b9cf8892826afc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/eprint_builtin_native_path_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/eprint_builtin_native_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/eprint_builtin_native_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the native runtime provider independent of the legacy spl provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a module calling eprint with zero diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats eprint like print: both lower with zero errors side by side' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
