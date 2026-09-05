# Numeric Interpolation Abi Specification

> Tests covering numeric interpolation tagged-handle ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Interpolation Abi Specification

## Scenarios

### numeric interpolation tagged-handle ABI

#### keeps numeric extremes and generic values correct in the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps numeric extremes and generic values correct in the interpreter
   - Expected: "min={minimum};max={maximum}" equals `min=-9223372036854775808;max=9223372036854775807`
   - Expected: generic_numeric_line(42) equals `generic=42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps numeric extremes and generic values correct in the interpreter")
val minimum: i64 = -9223372036854775807 - 1
val maximum: i64 = 9223372036854775807
expect("min={minimum};max={maximum}").to_equal("min=-9223372036854775808;max=9223372036854775807")
expect(generic_numeric_line(42)).to_equal("generic=42")
```

</details>

#### does not re-render a tagged scalar-text handle through str or concat

- does not re-render a tagged scalar-text handle through str or concat
   - Expected: direct_str_count_concat() equals `n=42`
   - Expected: reused_str_count_concat() equals `n=42;again=42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not re-render a tagged scalar-text handle through str or concat")
expect(direct_str_count_concat()).to_equal("n=42")
expect(reused_str_count_concat()).to_equal("n=42;again=42")
```

</details>

#### keeps tagged scalar text semantic across nested, mutable, method, container, and call boundaries

- keeps tagged scalar text semantic across nested, mutable, method, container, and call boundaries
   - Expected: nested_str_count() equals `42`
   - Expected: reassigned_str_count() equals `42`
   - Expected: tagged_text_methods() is true
   - Expected: tagged_text_container_round_trip() equals `42:42`
   - Expected: tagged_text_return_call() equals `42`
   - Expected: raw_text_return_call() equals `plain`
   - Expected: tagged_text_consumer_call() equals `count=42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps tagged scalar text semantic across nested, mutable, method, container, and call boundaries")
expect(nested_str_count()).to_equal("42")
expect(reassigned_str_count()).to_equal("42")
expect(tagged_text_methods()).to_equal(true)
expect(tagged_text_container_round_trip()).to_equal("42:42")
expect(tagged_text_return_call()).to_equal("42")
expect(raw_text_return_call()).to_equal("plain")
expect(tagged_text_consumer_call()).to_equal("count=42")
```

</details>

#### preserves every scalar renderer signature and SSA bridge into raw concatenation

- preserves every scalar renderer signature and SSA bridge into raw concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves every scalar renderer signature and SSA bridge into raw concatenation")
val llvm = compile_numeric_interpolation_fixture()
assert_true(not llvm.starts_with("MIR_LOWERING_ERRORS:"), "fixture failed to lower to MIR: " + llvm)
expect(llvm).to_contain("declare i64 @rt_raw_i64_to_string(i64)")
expect(llvm).to_contain("declare i64 @rt_raw_u64_to_string(i64)")
expect(llvm).to_contain("declare i64 @rt_raw_bool_to_string(i64)")
expect(llvm).to_contain("declare i64 @rt_raw_f64_to_string(double)")
expect(llvm).to_contain("declare ptr @rt_interp_cstr(i64)")

val i64_call = find_call_line(llvm, "rt_raw_i64_to_string(")
val u64_call = find_call_line(llvm, "rt_raw_u64_to_string(")
val bool_call = find_call_line(llvm, "rt_raw_bool_to_string(")
val f64_call = find_call_line(llvm, "rt_raw_f64_to_string(")
expect(i64_call).to_contain("= call i64 @rt_raw_i64_to_string(i64 ")
expect(u64_call).to_contain("= call i64 @rt_raw_u64_to_string(i64 ")
expect(bool_call).to_contain("= call i64 @rt_raw_bool_to_string(i64 ")
expect(f64_call).to_contain("= call i64 @rt_raw_f64_to_string(double ")

assert_true(renderer_cstr_strcat_flow(llvm, "rt_raw_i64_to_string"), "i64 renderer must flow through rt_interp_cstr into rt_strcat")
assert_true(renderer_cstr_strcat_flow(llvm, "rt_raw_u64_to_string"), "u64 renderer must flow through rt_interp_cstr into rt_strcat")
assert_true(renderer_cstr_strcat_flow(llvm, "rt_raw_bool_to_string"), "bool renderer must flow through rt_interp_cstr into rt_strcat")
assert_true(renderer_cstr_strcat_flow(llvm, "rt_raw_f64_to_string"), "f64 renderer must flow through rt_interp_cstr into rt_strcat")
assert_true(tagged_text_direct_param_flow(llvm), "tagged scalar text must bridge through rt_interp_cstr before a user text parameter")
```

</details>

#### survives two parser reset cycles after a large numeric diagnostic line

- survives two parser reset cycles after a large numeric diagnostic line
   - Expected: line equals `phase2:surface:file:start path=first.spl heap_registry=9223372036854775807`
   - Expected: parser_has_errors() is false
   - Expected: module_get_decls().len() equals `1`
   - Expected: parser_has_errors() is false
   - Expected: module_get_decls().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("survives two parser reset cycles after a large numeric diagnostic line")
val line = heap_registry_log_line("first.spl", 9223372036854775807)
expect(line).to_equal("phase2:surface:file:start path=first.spl heap_registry=9223372036854775807")

ast_reset()
parser_init_with_path("fn first() -> i64:\n    1\n", "first.spl")
parse_module_body()
expect(parser_has_errors()).to_equal(false)
expect(module_get_decls().len()).to_equal(1)

ast_reset()
parser_init_with_path("fn second() -> i64:\n    2\n", "second.spl")
parse_module_body()
expect(parser_has_errors()).to_equal(false)
expect(module_get_decls().len()).to_equal(1)
ast_reset()
```

</details>

#### keeps the focused native runtime probe aligned with this ABI contract

- keeps the focused native runtime probe aligned with this ABI contract
   - Expected: probe does not contain `fn generic_numeric_line<T>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the focused native runtime probe aligned with this ABI contract")
val probe = file_read("test/fixtures/compiler/native_numeric_interpolation_abi_probe.spl")
# Keep the executable probe narrow: its successful native-build/run
# verifies the numeric extrema and diagnostic shape. The in-process
# test above owns generic interpolation and parser_init_with_path /
# ast_reset cycles because native generic declarations remain an
# independently tracked unsupported feature.
expect(probe.contains("fn generic_numeric_line<T>")).to_equal(false)
expect(probe).to_contain("-9223372036854775808")
expect(probe).to_contain("heap_registry=807339")
expect(probe).to_contain("print(str(value))")
expect(probe).to_contain("str(str(value))")
expect(probe).to_contain("replacement = rendered")
expect(probe).to_contain("rendered.len() == 6")
expect(probe).to_contain("rendered.starts_with(\"807\")")
expect(probe).to_contain("val values: [text] = [rendered]")
expect(probe).to_contain("val named: Dict<text, text> = {\"count\": rendered}")
expect(probe).to_contain("tagged_text_identity(str(value))")
expect(probe).to_contain("tagged_text_consumer(str(value))")
expect(probe).to_contain("print_tagged_text(value) == 0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering numeric interpolation tagged-handle ABI.
- numeric interpolation tagged-handle ABI

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e84064afd4b379d38fac9e293362af365a31c60479e116cdb586141ef5e29dc9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e84064afd4b379d38fac9e293362af365a31c60479e116cdb586141ef5e29dc9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e84064afd4b379d38fac9e293362af365a31c60479e116cdb586141ef5e29dc9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/numeric_interpolation_abi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/numeric_interpolation_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/numeric_interpolation_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps numeric extremes and generic values correct in the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not re-render a tagged scalar-text handle through str or concat' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps tagged scalar text semantic across nested, mutable, method, container, and call boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
