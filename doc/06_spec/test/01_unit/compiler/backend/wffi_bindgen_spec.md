# Wffi Bindgen Specification

> <details>

<!-- sdn-diagram:id=wffi_bindgen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wffi_bindgen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wffi_bindgen_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wffi_bindgen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wffi Bindgen Specification

## Scenarios

### WFFI Bindgen

#### sanitizes library names into safe identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lib_name_to_safe("libm.so")).to_equal("m")
expect(lib_name_to_safe("libsqlite3.so.0")).to_equal("sqlite3")
expect(lib_name_to_safe("zlib.so")).to_equal("zlib")
```

</details>

#### maps wrapper call helpers by return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wffi_rt_call_fn("f64")).to_equal("rt_wffi_call_f64")
expect(wffi_rt_call_fn("i64")).to_equal("rt_wffi_call_i64")
expect(wffi_rt_call_fn("bool")).to_equal("rt_wffi_call_bool")
expect(wffi_rt_call_fn("text")).to_equal("rt_wffi_call_text")
expect(wffi_rt_call_fn("i32")).to_equal("rt_wffi_call_i32")
expect(wffi_rt_call_fn("custom")).to_equal("rt_wffi_call_i64")
```

</details>

#### formats parameter lists and names deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = sample_params()

expect(wffi_params_to_text(params)).to_equal("x: f64, count: i32")
expect(wffi_param_names_to_text(params)).to_equal("x, count")
expect(wffi_params_to_text([])).to_equal("")
expect(wffi_param_names_to_text([])).to_equal("")
```

</details>

#### builds bindings and loader text for a library

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. wffi binding new
2. sample fn
3. sample fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/backend/wffi_bindgen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
