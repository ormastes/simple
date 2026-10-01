# Dict Field Argument Transport Specification

> Tests covering interpreter aggregate-field argument transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Field Argument Transport Specification

## Scenarios

### interpreter aggregate-field argument transport

#### preserves dictionary and array fields through free and method calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves dictionary and array fields through free and method calls
   - Expected: free_dict_count(values) equals `1`
   - Expected: free_dict_count(source.values) equals `1`
   - Expected: sink.dict_count(values) equals `1`
   - Expected: sink.dict_count(source.values) equals `1`
   - Expected: sink.array_count(source.names) equals `1`
   - Expected: sink.multi_dict_count("gpu", source.values, orders) equals `2`
   - Expected: free_aggregate_dict_count(source) equals `1`
   - Expected: sink.aggregate_dict_count(source) equals `1`
   - Expected: sink.aggregate_array_count(source) equals `1`
   - Expected: source.receiver_head_dict_count() equals `1`
   - Expected: source.receiver_tail_dict_count() equals `1`
   - Expected: source.receiver_tail_array_count() equals `1`
   - Expected: source.receiver_tail_dict_count() equals `1`
   - Expected: source.receiver_tail_array_count() equals `1`
   - Expected: sink.dict_count(values_local) equals `1`
   - Expected: sink.array_count(names_local) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves dictionary and array fields through free and method calls")
var values: Dict<text, text> = {}
values["copy"] = "vulkan"
var source = DictFieldTransportProbe.new(values, ["copy"])
var sink = DictFieldTransportProbe.new({}, [])

expect(free_dict_count(values)).to_equal(1)
expect(free_dict_count(source.values)).to_equal(1)
expect(sink.dict_count(values)).to_equal(1)
expect(sink.dict_count(source.values)).to_equal(1)
expect(sink.array_count(source.names)).to_equal(1)

var orders: Dict<text, text> = {}
orders["copy"] = "cuda,vulkan"
expect(sink.multi_dict_count("gpu", source.values, orders)).to_equal(2)
expect(free_aggregate_dict_count(source)).to_equal(1)
expect(sink.aggregate_dict_count(source)).to_equal(1)
expect(sink.aggregate_array_count(source)).to_equal(1)
expect(source.receiver_head_dict_count()).to_equal(1)
expect(source.receiver_tail_dict_count()).to_equal(1)
expect(source.receiver_tail_array_count()).to_equal(1)

var replacement_values: Dict<text, text> = {}
replacement_values["dispatch"] = "metal"
val replacement_names = ["dispatch"]
source.tail_values = replacement_values
source.tail_names = replacement_names
expect(source.receiver_tail_dict_count()).to_equal(1)
expect(source.receiver_tail_array_count()).to_equal(1)

val values_local = source.values
val names_local = source.names
expect(sink.dict_count(values_local)).to_equal(1)
expect(sink.array_count(names_local)).to_equal(1)
```

</details>

#### preserves nested tail metadata through Dict.values and method forwarding

- preserves nested tail metadata through Dict.values and method forwarding
   - Expected: free_nested_module_backend_order(module) equals `rocm,cl,cuda`
   - Expected: sink.nested_module_backend_order(module) equals `rocm,cl,cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves nested tail metadata through Dict.values and method forwarding")
val attr = NestedGpuAttrProbe(
    is_entry: false, is_naked: false, is_noreturn: false, section: nil,
    is_interrupt: false, is_boot: false, is_alloc: false, is_no_alloc: false,
    is_gpu_kernel: true, gpu_target: "auto", gpu_backends: "rocm,cl,cuda"
)
val function = NestedGpuFunctionProbe(
    name: "copy", attr: attr, is_gpu_kernel: true,
    gpu_target: "auto", gpu_backend_order: "rocm,cl,cuda"
)
var functions: Dict<text, NestedGpuFunctionProbe> = {}
functions["copy"] = function
val module = NestedGpuModuleProbe(name: "gpu", functions: functions)
val sink = DictFieldTransportProbe.new({}, [])

expect(free_nested_module_backend_order(module)).to_equal("rocm,cl,cuda")
expect(sink.nested_module_backend_order(module)).to_equal("rocm,cl,cuda")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter aggregate-field argument transport.
- interpreter aggregate-field argument transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `5c01708baf1dceccdbd2cf7fa4d441af1bd83cf10fbb1e445429e2a292b29673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c01708baf1dceccdbd2cf7fa4d441af1bd83cf10fbb1e445429e2a292b29673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c01708baf1dceccdbd2cf7fa4d441af1bd83cf10fbb1e445429e2a292b29673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/dict_field_argument_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/dict_field_argument_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/dict_field_argument_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves dictionary and array fields through free and method calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl:227:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested tail metadata through Dict.values and method forwarding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
