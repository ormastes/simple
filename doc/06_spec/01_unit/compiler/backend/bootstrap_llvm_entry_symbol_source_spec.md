# Bootstrap Llvm Entry Symbol Source Specification

> Tests covering bootstrap LLVM entry symbol source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Llvm Entry Symbol Source Specification

## Scenarios

### bootstrap LLVM entry symbol source

#### uses plain function definitions for bootstrap objects

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses plain function definitions for bootstrap objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses plain function definitions for bootstrap objects")
val source = mir_to_llvm_core_source()

expect(source).to_contain("(rt_env_get(\"SIMPLE_BOOTSTRAP\") ?? \"\") == \"1\"")
expect(source).to_contain("self.builder.start_function_opt(fn_name, params, ret_ty, is_readonly, is_small)")
```

</details>

#### tracks bootstrap function-local definitions

- tracks bootstrap function-local definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks bootstrap function-local definitions")
val source = mir_to_llvm_core_source()

expect(source).to_contain("self.defined_locals = {}")
expect(source).to_contain("self.bool_locals = {}")
expect(source).to_contain("self.ptr_locals = {}")
expect(source).to_contain("self.local_types = {}")
```

</details>

#### links bootstrap LLVM with runtime argv and non-pie objects

- links bootstrap LLVM with runtime argv and non-pie objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("links bootstrap LLVM with runtime argv and non-pie objects")
val source = mir_to_llvm_core_source()
val driver = driver_bootstrap_source()
val linker = linker_native_source()
val tools = llvm_backend_tools_source()

expect(source).to_contain("val bare_name_for_call = if func_name.starts_with(\"@\")")
expect(source).to_contain("var call_func_name = if bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\": \"@rt_get_args\" elif bare_name_for_call == \"env_get\": \"@rt_env_get\" elif bare_name_for_call == \"eprint\": \"@rt_eprint\" else: func_name")
expect(source).to_contain("elif bare_func_name == \"rt_get_args\":")
expect(linker).to_contain("args.push(\"-no-pie\")")
expect(tools).to_contain("--relocation-model=pic --function-sections --data-sections")
expect(tools).to_contain("if llc_code != 0:")
```

</details>

#### remaps env_get to rt_env_get and keeps runtime declaration consistent

- remaps env_get to rt_env_get and keeps runtime declaration consistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remaps env_get to rt_env_get and keeps runtime declaration consistent")
val source = mir_to_llvm_core_source()
val helpers = rt_file_read_text("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl") ?? ""
val runtime_decls = llvm_backend_source()

expect(source).to_contain("var call_func_name = if bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\": \"@rt_get_args\" elif bare_name_for_call == \"env_get\": \"@rt_env_get\" elif bare_name_for_call == \"eprint\": \"@rt_eprint\" else: func_name")
expect(source).to_contain("elif bare_func_name == \"env_get\" or bare_func_name == \"rt_env_get\":")
expect(helpers).to_contain("declare ptr @rt_env_get(...)")
expect(source).to_not_contain("declare ptr @env_get")
expect(runtime_decls).to_contain("declare ptr @rt_array_get(ptr, i64)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap LLVM entry symbol source.
- bootstrap LLVM entry symbol source

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `27e4e72d2d0cc2536e8a7786133c043c4545653ada542e2576ecfe6d6212d379`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27e4e72d2d0cc2536e8a7786133c043c4545653ada542e2576ecfe6d6212d379`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27e4e72d2d0cc2536e8a7786133c043c4545653ada542e2576ecfe6d6212d379`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses plain function definitions for bootstrap objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks bootstrap function-local definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links bootstrap LLVM with runtime argv and non-pie objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
