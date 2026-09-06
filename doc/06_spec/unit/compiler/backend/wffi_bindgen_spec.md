# Wffi Bindgen Specification

> Tests covering WFFI Bindgen.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wffi Bindgen Specification

## Scenarios

### WFFI Bindgen

#### sanitizes library names into safe identifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sanitizes library names into safe identifiers
   - Expected: lib_name_to_safe("libm.so") equals `m`
   - Expected: lib_name_to_safe("libsqlite3.so.0") equals `sqlite3`
   - Expected: lib_name_to_safe("zlib.so") equals `zlib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitizes library names into safe identifiers")
expect(lib_name_to_safe("libm.so")).to_equal("m")
expect(lib_name_to_safe("libsqlite3.so.0")).to_equal("sqlite3")
expect(lib_name_to_safe("zlib.so")).to_equal("zlib")
```

</details>

#### maps wrapper call helpers by return type

- maps wrapper call helpers by return type
   - Expected: wffi_rt_call_fn("f64") equals `rt_wffi_call_f64`
   - Expected: wffi_rt_call_fn("i64") equals `rt_wffi_call_i64`
   - Expected: wffi_rt_call_fn("bool") equals `rt_wffi_call_bool`
   - Expected: wffi_rt_call_fn("text") equals `rt_wffi_call_text`
   - Expected: wffi_rt_call_fn("i32") equals `rt_wffi_call_i32`
   - Expected: wffi_rt_call_fn("custom") equals `rt_wffi_call_i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps wrapper call helpers by return type")
expect(wffi_rt_call_fn("f64")).to_equal("rt_wffi_call_f64")
expect(wffi_rt_call_fn("i64")).to_equal("rt_wffi_call_i64")
expect(wffi_rt_call_fn("bool")).to_equal("rt_wffi_call_bool")
expect(wffi_rt_call_fn("text")).to_equal("rt_wffi_call_text")
expect(wffi_rt_call_fn("i32")).to_equal("rt_wffi_call_i32")
expect(wffi_rt_call_fn("custom")).to_equal("rt_wffi_call_i64")
```

</details>

#### formats parameter lists and names deterministically

- formats parameter lists and names deterministically
   - Expected: wffi_params_to_text(params) equals `x: f64, count: i32`
   - Expected: wffi_param_names_to_text(params) equals `x, count`
   - Expected: wffi_params_to_text([]) equals ``
   - Expected: wffi_param_names_to_text([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats parameter lists and names deterministically")
val params = sample_params()

expect(wffi_params_to_text(params)).to_equal("x: f64, count: i32")
expect(wffi_param_names_to_text(params)).to_equal("x, count")
expect(wffi_params_to_text([])).to_equal("")
expect(wffi_param_names_to_text([])).to_equal("")
```

</details>

#### builds bindings and loader text for a library

- builds bindings and loader text for a library
   - Expected: binding.lib_name equals `libm.so`
   - Expected: binding.handle_var equals `wffi_m_handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds bindings and loader text for a library")
val binding = wffi_binding_new("libm.so")
val output = wffi_generate_loader(binding)

expect(binding.lib_name).to_equal("libm.so")
expect(binding.handle_var).to_equal("wffi_m_handle")
expect(output).to_contain("fn wffi_load_m() -> i64:")
expect(output).to_contain("rt_wffi_load(\"libm.so\")")
expect(output).to_contain("var wffi_m_handle: i64 = 0")
expect(output).to_contain("fn m_init():")
```

</details>

#### generates wrappers and complete wrapper bundles

- generates wrappers and complete wrapper bundles


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates wrappers and complete wrapper bundles")
val binding = wffi_binding_add_fn(
    wffi_binding_new("libm.so"),
    sample_fn("sqrt", true, "f64")
)
val binding2 = wffi_binding_add_fn(
    binding,
    sample_fn("sink", false, "i64")
)

val sqrt_code = wffi_generate_function(binding2, binding2.functions[0])
val sink_code = wffi_generate_function(binding2, binding2.functions[1])
val bundle = generate_wffi_wrappers(binding2)

expect(sqrt_code).to_contain("fn sqrt(x: f64, count: i32) -> f64:")
expect(sqrt_code).to_contain("rt_wffi_call_f64(wffi_m_handle, \"sqrt\", x, count)")
expect(sink_code).to_contain("fn sink(x: f64, count: i32):")
expect(sink_code).to_contain("rt_wffi_call_void(wffi_m_handle, \"sink\", x, count)")
expect(bundle).to_contain("# Auto-generated WFFI wrappers for libm.so")
expect(bundle).to_contain("fn wffi_load_m() -> i64:")
expect(bundle).to_contain("fn sqrt(x: f64, count: i32) -> f64:")
expect(bundle).to_contain("fn sink(x: f64, count: i32):")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/wffi_bindgen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WFFI Bindgen.
- WFFI Bindgen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f14dedce7545282052343c7d86cdbfcf5cae727448c639f1f6c3b89cffd559fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f14dedce7545282052343c7d86cdbfcf5cae727448c639f1f6c3b89cffd559fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f14dedce7545282052343c7d86cdbfcf5cae727448c639f1f6c3b89cffd559fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/wffi_bindgen_spec.spl
mirror: doc/06_spec/unit/compiler/backend/wffi_bindgen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/wffi_bindgen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/wffi_bindgen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/wffi_bindgen_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sanitizes library names into safe identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/wffi_bindgen_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps wrapper call helpers by return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/wffi_bindgen_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats parameter lists and names deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
