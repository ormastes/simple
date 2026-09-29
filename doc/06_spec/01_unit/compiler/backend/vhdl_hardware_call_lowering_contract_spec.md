# Vhdl Hardware Call Lowering Contract Specification

> Tests covering VHDL direct hardware calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Hardware Call Lowering Contract Specification

## Scenarios

### VHDL direct hardware calls

#### wires a renamed pure helper call into its own typed instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile a clocked top that calls a renamed pure helper and inspect the emitted VHDL
   - Expected: result.is_ok() is true
   - Expected: vhdl contains `simple_hwcall_comb_helper_0: entity work.comb_helper`
   - Expected: vhdl contains `state => state_in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a clocked top that calls a renamed pure helper and inspect the emitted VHDL")
val result = backend().compile(renamed_callee_module())
expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl.contains("simple_hwcall_comb_helper_0: entity work.comb_helper")).to_equal(true)
expect(vhdl.index_of("entity comb_helper is")).to_be_less_than(vhdl.index_of("entity renamed_top is"))
expect(vhdl.contains("state => state_in")).to_equal(true)
```

</details>

#### instantiates a typed entity outside the clocked process

- instantiates a typed entity outside the clocked process
   - Expected: result.is_ok() is true
   - Expected: vhdl contains `signal simple_hwcall_transition_0_result_out : signed(31 downto 0);`
   - Expected: vhdl contains `simple_hwcall_transition_0: entity work.transition`
   - Expected: vhdl contains `state => state_in`
   - Expected: vhdl contains `result_out => simple_hwcall_transition_0_result_out`
   - Expected: vhdl contains `result_out <= simple_hwcall_transition_0_result_out;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("instantiates a typed entity outside the clocked process")
val result = backend().compile(call_module(false))
expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl.contains("signal simple_hwcall_transition_0_result_out : signed(31 downto 0);")).to_equal(true)
expect(vhdl.contains("simple_hwcall_transition_0: entity work.transition")).to_equal(true)
expect(vhdl.contains("state => state_in")).to_equal(true)
expect(vhdl.contains("result_out => simple_hwcall_transition_0_result_out")).to_equal(true)
expect(vhdl.contains("result_out <= simple_hwcall_transition_0_result_out;")).to_equal(true)
expect(vhdl.index_of("entity transition is")).to_be_less_than(vhdl.index_of("entity clocked_top is"))
```

</details>

#### orders record callees before a reset-owned clocked state entry

- orders record callees before a reset-owned clocked state entry
   - Expected: result.is_ok() is true
   - Expected: vhdl contains `signal simple_hwcall_reset_transition_0_result_out : cycle_result_t;`
   - Expected: vhdl contains `signal simple_hwcall_cycle_transition_1_result_out : cycle_result_t;`
   - Expected: vhdl contains `signal global_state : signed(31 downto 0);`
   - Expected: vhdl contains `state => global_state`
   - Expected: vhdl contains `p_clk: process(clk)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders record callees before a reset-owned clocked state entry")
val result = backend().compile(record_clocked_module())
expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl.index_of("entity reset_transition is")).to_be_less_than(vhdl.index_of("entity record_clocked_top is"))
expect(vhdl.index_of("entity cycle_transition is")).to_be_less_than(vhdl.index_of("entity record_clocked_top is"))
expect(vhdl.contains("signal simple_hwcall_reset_transition_0_result_out : cycle_result_t;")).to_equal(true)
expect(vhdl.contains("signal simple_hwcall_cycle_transition_1_result_out : cycle_result_t;")).to_equal(true)
expect(vhdl.contains("signal global_state : signed(31 downto 0);")).to_equal(true)
expect(vhdl.contains("state => global_state")).to_equal(true)
expect(vhdl.contains("p_clk: process(clk)")).to_equal(true)
```

</details>

#### rejects duplicate call-result definitions across branches

- rejects duplicate call-result definitions across branches
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err().message contains `one definition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects duplicate call-result definitions across branches")
val result = backend().compile(duplicate_dest_module(false))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message.contains("one definition")).to_equal(true)
```

</details>

#### rejects branch-local call input definitions

- rejects branch-local call input definitions
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err().message contains `unconditional architecture-visible definition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects branch-local call input definitions")
val result = backend().compile(duplicate_dest_module(true))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message.contains("unconditional architecture-visible definition")).to_equal(true)
```

</details>

#### rejects entity generics without an explicit generic map

- rejects entity generics without an explicit generic map
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err().message contains `no explicit generic map`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects entity generics without an explicit generic map")
var module = call_module(false)
val symbol = SymbolId(id: 800)
var transition = module.functions[symbol]
var metadata = transition.vhdl_metadata
metadata.generics = [VhdlGenericMetadata(name: "WIDTH", type_text: "natural", default_text: "32")]
transition.vhdl_metadata = metadata
module.functions[symbol] = transition
val result = backend().compile(module)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message.contains("no explicit generic map")).to_equal(true)
```

</details>

#### rejects recursive entity call graphs

- rejects recursive entity call graphs
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err().message contains `call cycle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects recursive entity call graphs")
val result = backend().compile(call_module(true))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message.contains("call cycle")).to_equal(true)
```

</details>

#### renders an immutable BinOp SSA argument directly into the port map

- renders an immutable BinOp SSA argument directly into the port map
   - Expected: result.is_ok() is true
   - Expected: vhdl contains `state => (left + right)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders an immutable BinOp SSA argument directly into the port map")
val result = backend().compile(pure_ssa_call_module())
expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl.contains("state => (left + right)")).to_equal(true)
```

</details>

#### suffixes generated instance labels that collide with a port name

- suffixes generated instance labels that collide with a port name
   - Expected: result.is_ok() is true
   - Expected: vhdl contains `simple_hwcall_transition_0_1: entity work.transition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("suffixes generated instance labels that collide with a port name")
val result = backend().compile(instance_collision_module())
expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl.contains("simple_hwcall_transition_0_1: entity work.transition")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL direct hardware calls.
- VHDL direct hardware calls

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63b51922f01929c7ee3aa0e08be1b2d17447bf2e4d42be0db33c3927b9d07b75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63b51922f01929c7ee3aa0e08be1b2d17447bf2e4d42be0db33c3927b9d07b75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63b51922f01929c7ee3aa0e08be1b2d17447bf2e4d42be0db33c3927b9d07b75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.spl:244:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires a renamed pure helper call into its own typed instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.spl:254:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'instantiates a typed entity outside the clocked process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_hardware_call_lowering_contract_spec.spl:267:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders record callees before a reset-owned clocked state entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
