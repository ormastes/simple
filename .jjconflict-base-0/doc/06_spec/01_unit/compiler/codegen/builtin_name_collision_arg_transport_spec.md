# Builtin Name Collision Arg Transport Specification

> Tests covering user methods named after builtins keep their own argument transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Builtin Name Collision Arg Transport Specification

## Scenarios

### user methods named after builtins keep their own argument transport

#### round-trips an integer argument through every special-cased method name on the JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips an integer argument through every special-cased method name on the JIT
- Run the class probe under SIMPLE_EXECUTION_MODE=jit
- Array mutator names — `push`/`append` are the confirmed instance (42 arrived as 336)
- Search and accessor names that share the same rewrite machinery
- Dict and text names
- Floats travel a different boxing path (BoxFloat) and must be gated identically
- Control arm — the genuine builtins must still round-trip after any gate is added
- The aggregate verdict line is authoritative
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips an integer argument through every special-cased method name on the JIT")
step("Run the class probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("Array mutator names — `push`/`append` are the confirmed instance (42 arrived as 336)")
expect(jit).to_contain("PASS push")
expect(jit).to_contain("PASS append")
expect(jit).to_contain("PASS insert")
expect(jit).to_contain("PASS extend")
expect(jit).to_contain("PASS remove")
expect(jit).to_contain("PASS write_span")

step("Search and accessor names that share the same rewrite machinery")
expect(jit).to_contain("PASS index_of")
expect(jit).to_contain("PASS contains")
expect(jit).to_contain("PASS at")
expect(jit).to_contain("PASS char_at")
expect(jit).to_contain("PASS byte_at")

step("Dict and text names")
expect(jit).to_contain("PASS get")
expect(jit).to_contain("PASS set")
expect(jit).to_contain("PASS merge")
expect(jit).to_contain("PASS concat")
expect(jit).to_contain("PASS join")
expect(jit).to_contain("PASS split")
expect(jit).to_contain("PASS replace")
expect(jit).to_contain("PASS repeat")

step("Floats travel a different boxing path (BoxFloat) and must be gated identically")
expect(jit).to_contain("PASS push_f64")
expect(jit).to_contain("PASS append_f64")

step("Control arm — the genuine builtins must still round-trip after any gate is added")
expect(jit).to_contain("PASS builtin_array_push_roundtrip")
expect(jit).to_contain("PASS builtin_array_push_f64_roundtrip")
expect(jit).to_contain("PASS builtin_array_index_of")
expect(jit).to_contain("PASS builtin_text_index_of")

step("The aggregate verdict line is authoritative")
expect(jit).to_contain("BUILTIN_NAME_COLLISION PROBE: ALL PASS")
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

#### reports exactly the known-open sibling defect and no more

- reports exactly the known-open sibling defect and no more
- `char_code_at` on a struct receiver is stolen outright by rt_string_char_code_at (returns 0). That is codegen suffix resolution, a separate root cause, filed separately — it is counted on its own line so it can neither be silently dropped nor mask a new regression.


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports exactly the known-open sibling defect and no more")
step("`char_code_at` on a struct receiver is stolen outright by rt_string_char_code_at (returns 0). That is codegen suffix resolution, a separate root cause, filed separately — it is counted on its own line so it can neither be silently dropped nor mask a new regression.")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("BUILTIN_NAME_COLLISION KNOWN-OPEN COUNT: 1")
```

</details>

#### is correct on the tree-walk interpreter, the control engine

- is correct on the tree-walk interpreter, the control engine
- The interpreter never exhibited this class; a red here means the probe is broken, not the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is correct on the tree-walk interpreter, the control engine")
step("The interpreter never exhibited this class; a red here means the probe is broken, not the engine")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("BUILTIN_NAME_COLLISION PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering user methods named after builtins keep their own argument transport.
- user methods named after builtins keep their own argument transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `d9f7e01b989ffd060a538f3ac884d235200113b35aca02b63c7580680dd683f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d9f7e01b989ffd060a538f3ac884d235200113b35aca02b63c7580680dd683f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d9f7e01b989ffd060a538f3ac884d235200113b35aca02b63c7580680dd683f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips an integer argument through every special-cased method name on the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports exactly the known-open sibling defect and no more' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is correct on the tree-walk interpreter, the control engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
