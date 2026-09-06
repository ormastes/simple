<!-- codex-design -->
# RISC-V scalar runtime pipeline v5: implementation binding manifest

Status: **normative implementation contract; direct prefix is endpoint-checked,
but not an implemented-netlist claim**.
This companion freezes the replacement for the prose v5 binding plan.  It is
code-neutral: a renderer or a later typed composition builder must consume this
manifest, validate it, and emit it.  Existing v5 constructors currently create
children only; they do **not** yet materialize this binding list or prove that
the listed source wiring exists.

## 1. Parameters, identity, and schema

`X = CoreConfig.xlen` (`32` or `64`); `PA = CoreConfig.physical_address_bits`;
`B = LsuConfig.bus_data_bits = X`; and `MASK = LsuConfig.byte_mask_bits = B/8`
(`4` for the supplied RV32 default, `8` for RV64). `ROW = ceil_log2(plan row
count + 1)` using the decoded-uop v1 algorithm (start width/capacity at `1/2`,
increment while `capacity <= row_count`). Every endpoint is `Bits[width]`.

The artifact schema is `hwir-riscv-scalar-runtime-binding/v5`. Its identity is
the ordered concatenation of schema ID, module name, complete CoreConfig,
complete LsuConfig, decoder-plan hash, decoded-uop schema hash, completion-v1
schema hash, each child receipt `(owner, graph hash)`, ordered top ports,
ordered field groups, ordered defaults, ordered bindings, fault policy, and
renderer receipt. Case-sensitive owner and port names are identity material.
Duplicate destination, duplicate top port, alias, missing ordered entry,
unknown endpoint, wrong direction, or unequal width is rejection.

## 2. Exact top ABI, in this order

Inputs: `clk:1`, `rst:1`, `in_valid:1`, `instruction:32`,
`instruction_length_bytes:3`, `rs1_value:X`, `rs2_value:X`, `pc_before:X`,
`fallthrough_pc:X`, `privilege:2`, `provider_event_id:64`,
`decode_event_id:64`, `completion_ready:1`, `bus_request_ready:1`,
`bus_response_valid:1`, `bus_response_id:64`, `bus_response_data:B`,
`bus_response_fault:1`, `bus_response_cause:X`, `bus_response_tval:X`,
`fence_effect_ready:1`.

Outputs: `in_ready:1`; `completion_valid:1`; then completion-v1 payload in
this exact order: `completion_privilege:2`, `completion_original_instruction:32`,
`completion_canonical_instruction:32`, `completion_instruction_length_bytes:3`,
`completion_pc_before:X`, `completion_pc_after:X`, `completion_rd:5`,
`completion_rd_write:1`, `completion_rd_value:X`, `completion_memory_address:X`,
`completion_memory_read_mask:32`, `completion_memory_write_mask:32`,
`completion_memory_read_data:X`, `completion_memory_write_data:X`,
`completion_execute_trap_valid:1`, `completion_execute_trap_cause:X`,
`completion_execute_trap_tval:X`, `completion_memory_trap_valid:1`,
`completion_memory_trap_cause:X`, `completion_memory_trap_tval:X`,
`completion_redirect_valid:1`, `completion_redirect_target:X`; then
`completion_provider_event_id:64`, `completion_decode_event_id:64`,
`completion_illegal_valid:1`; then
`runtime_protocol_fault:1`, `bus_request_valid:1`, `bus_request_id:64`,
`bus_request_address:PA`, `bus_request_write:1`, `bus_request_byte_mask:MASK`,
`bus_request_write_data:B`, `bus_response_ready:1`, `fence_effect_valid:1`,
`fence_effect_kind:2`, `fence_effect_fm:4`, `fence_effect_pred:4`,
`fence_effect_succ:4`.

No other child endpoint is public, including accepts, child ready signals,
provider tags, selector controls, decoder outputs, pending state, or raw fault
signals.

## 3. Field groups and ordered binding expansion

The following symbols expand at their shown position; a `GROUP` binding means
one binding per field in the exact listed order, with no renaming.

* `UOP = [uop_valid:1, decode_legal:1, decoded_row_index:ROW,
  decoded_execution_class:3, decoded_memory_effect:3, decoded_semantic_opcode:6,
  decoded_declared_operand_width_is_32:1, canonical_instruction:32,
  original_instruction:32, instruction_length_bytes:3, instruction_rd_field:5,
  instruction_rs1_field:5, instruction_rs2_field:5, rs1_value:X, rs2_value:X,
  pc_before:X, fallthrough_pc:X, privilege:2, provider_event_id:64,
  decode_event_id:64, lineage_valid:1]`.
* `C = [privilege:2, original_instruction:32, canonical_instruction:32,
  instruction_length_bytes:3, pc_before:X, pc_after:X, rd:5, rd_write:1,
  rd_value:X, memory_address:X, memory_read_mask:32, memory_write_mask:32,
  memory_read_data:X, memory_write_data:X, execute_trap_valid:1,
  execute_trap_cause:X, execute_trap_tval:X, memory_trap_valid:1,
  memory_trap_cause:X, memory_trap_tval:X, redirect_valid:1,
  redirect_target:X, provider_event_id:64, decode_event_id:64, illegal_valid:1]`.
  The first 22 fields are completion-v1 payload; the final three are merger
  lineage fields and never appear in the top completion ABI.
* `CTX = [instruction:32, instruction_length_bytes:3, rs1_value:X, rs2_value:X,
  pc_before:X, fallthrough_pc:X, privilege:2, provider_event_id:64,
  decode_event_id:64]`.

The canonical binding rows, in order, are:

1. `top.clk/rst -> uop_skid.clk/rst`, `pending.clk/rst`, `lsu.clk/rst`,
   `fence.clk/rst`, `completion_skid.clk/rst`, and `fault_owner.clk/rst`;
   `top.in_valid -> uop_skid.upstream_valid`; each `CTX` member expands to
   `top.<field> -> uop_skid.upstream_<field>` (except `instruction`, which is
   `top.instruction -> decoder.instruction` and
   `top.instruction -> uop_skid.upstream_original_instruction`); each decoder
   output expands to its actual matching `uop_skid.upstream_` input: `decoded_valid`,
   `decoded_row_index`, `decoded_execution_class`, `decoded_memory_effect`,
   `decoded_semantic_opcode`, `decoded_operand_width_32 ->
   upstream_decoded_declared_operand_width_is_32`, `canonical_instruction`,
   `instruction_rd_field`, `instruction_rs1_field`, and `instruction_rs2_field`.
   `uop_skid` is the sole source of every subsequent decoded context.
2. `uop_skid.[uop_valid,decode_legal,illegal_valid,decoded_execution_class] ->
   router.[uop_valid,decode_legal,illegal_valid,decoded_execution_class]`;
   `pending.dispatch_ready -> router.pending_ready`; `pending.busy ->
   router.pending_busy`; immediate provider `*_ready` signals map to the four
   router ready inputs; `router.uop_ready -> uop_skid.uop_ready`; and
   `uop_skid.upstream_ready -> gate.raw_input_ready -> top.in_ready` (gated by
   the fault policy). `fault_owner.protocol_fault -> router` admission inhibit
   is a required materialized binding in the direct product.

   Pending-owner busy is an explicit one-bit output with the frozen equation
   `pending_reg || issued_reg || full_reg || fault_reg`. It is low only after
   reset or after an accepted completion has been consumed; sticky fault keeps
   it high (unavailable) until reset.
3. Router `alu/control/system/illegal_lane_valid -> immediate_adapter` matching
   inputs; adapter `selector_uop_valid -> selector.uop_valid`; router lane
   valids plus `uop_skid.UOP -> alu/control/system/illegal` corresponding inputs.
   The direct seam uses the typed v5 immediate selector: it receives all four
   completion/fault/`C` lanes and invariant held-uop context. `pc_after` stays
   provider-authored so redirects and precise traps are valid.
   `completion_merge.immediate_ready -> selector.completion_ready` is the one
   shared immediate completion-capacity edge; router alone owns skid readiness.
4. `router.pending_dispatch_valid/tag -> pending.dispatch_valid/tag`; each held
   pending dispatch field expands by exact lane prefix: `pending.lsu_request_<f>
   -> projection.<f>` for projection inputs, `pending.lsu_request_<f> ->
   lsu.request_<f>` for LSU request metadata, and `pending.fence_request_<f> ->
   fence.<f>` for each FENCE request input. The `f` field names are the frozen
   UOP/CTX names above; `pending.lsu_request_valid -> projection.uop_valid` and
   `pending.fence_request_valid -> fence.request_valid` are explicit aliases.
   `projection.* -> lsu.projection_*`; LSU and FENCE request-ready/accept and
   full completion/tag/fault endpoints return only through `pending`. The two
   provider completion-ready edges are explicit: `pending.lsu_completion_ready
   -> lsu.completion_ready` and `pending.fence_completion_ready ->
   fence.completion_ready`. Generic completion payload loops exclude
   `provider_event_id` and `decode_event_id`; pending's frozen aliases are
   `*_completion_event_id` and `*_completion_decode_event_id`.
   Router `legal_uop` qualification prohibits stateful dispatch of an illegal
   uop; `zero_defaults.zero_1` therefore supplies typed zero to
   `lsu.request_illegal_valid` and `fence.illegal_valid`.
   `completion_merge.pending_ready -> pending.completion_ready`.
5. `selector.[selected_valid,selected_C] -> completion_merge.[immediate_valid,
   immediate_C]`; `pending.[completion_valid,completion_C] ->
   completion_merge.[pending_valid,pending_C]`; both provider faults map to the
   corresponding merge fault inputs; `completion_skid.upstream_ready ->
   completion_merge.skid_upstream_ready`; merge selected valid and `C` map to
   skid upstream. The skid maps the complete normalized completion envelope to
   top outputs, including provider/decode event IDs and illegal lineage;
   `top.completion_ready -> gate.raw_completion_ready ->
   gate.completion_ready -> completion_skid.downstream_ready`.
6. Raw LSU bus inputs and raw FENCE ready pass through the global fault gate to
   those owners. The gate carries only handshake booleans. Payload rows are
   always explicit: `lsu.bus_request_id/address/write/byte_mask/write_data ->
   top.bus_request_id/address/write/byte_mask/write_data`; `fence.fence_effect_kind/fm/pred/succ
   -> top.fence_effect_kind/fm/pred/succ`. Raw LSU request-valid/response-ready
   and raw FENCE effect-valid pass through the gate to the matching top ABI.
   `gate.input_ready -> top.in_ready` and `gate.completion_valid ->
   top.completion_valid` qualify, rather than replace, the skid signals.

## 4. Explicit defaults

All defaults are literal zero of the destination width, never undriven or
implicit: every MulDiv request/control/payload input; every CSR
request/control/payload input; unused pending tags 2 and 3; nonselected
provider valid/fault/C inputs; nonselected merge `C`; disabled bus request
payload (`id:64,address:PA,write:1,byte_mask:MASK,write_data:B`); disabled
fence payload (`kind:2,fm:4,pred:4,succ:4`); and completion payload whenever
the completion skid is invalid. Defaults are data defaults only: they do not
turn an unsupported provider into an accepted transaction.

## 5. Fault, reset, and transaction policy

Raw fault sources must connect to gate inputs exactly as follows:

| Source | Gate input |
|---|---|
| `router.router_fault` | `router_fault` |
| `uop_skid.protocol_fault` | `decoded_uop_skid_fault` |
| `immediate_adapter.adapter_fault` | `adapter_fault` |
| `selector.selector_fault` | `selector_fault` |
| `pending.protocol_fault` | `pending_fault` |
| `projection.protocol_fault` | `projection_fault` |
| `lsu.provider_protocol_fault` | `lsu_fault` |
| `fence.provider_protocol_fault` | `fence_fault` |
| `completion_merge.merge_fault` | `merge_fault` |
| `completion_skid.protocol_fault` | `completion_skid_fault` |

`gate.fault_in -> fault_owner.fault_in`; `fault_owner.protocol_fault ->
gate.sticky_fault`; and `fault_owner.protocol_fault -> top.runtime_protocol_fault`.
ALU/control/system/illegal fault reports must be folded into the selector's
`selector_fault`; they are not additional gate pins. The gate ORs the ten raw
sources; the sequential owner latches the result on the next active clock edge.
It resets synchronously with active-high `rst`; reset clears uop skid, pending,
LSU, FENCE, completion skid, and fault owner together. The current v5 seam is
terminal fail-stop until synchronous reset, not an in-band cancellation owner:
request/effect valid is suppressed,
response-ready is suppressed, completion-valid is suppressed, and no response
or effect may be emitted after reset. A producer sharing no reset is rejected.

On a raw fault before that edge, the gate immediately suppresses admission,
completion, bus request/response handshake, and fence effect handshake. After
the edge, sticky feedback keeps all of them suppressed until reset. A held
completion is **not drained** under fault; it is discarded only by the shared
synchronous reset epoch, and its payload is not architecturally observable.
A bus response received while faulted is not accepted; a fence effect is not
asserted while faulted. This is intentional
fail-stop behavior, not a completion-with-error protocol.

## 6. Renderer receipt manifest

A successful renderer must return `HwirScalarRuntimeV5RenderReceipt`:
`schema_id`, `module_name`, `core_config_hash`, `lsu_config_hash`,
`decoder_plan_hash`, `decoded_uop_schema_hash`, `completion_schema_hash`,
ordered `(owner, child_graph_hash)` list, `top_abi_hash`, `binding_list_hash`,
`default_list_hash`, `fault_policy_hash`, `rendered_vhdl_sha256`, and
`total_driver_count`. It additionally records `source_wiring_status` fixed to
`"manifest-validated-not-source-wired"` until a typed composition implementation
proves the bindings. Rendering fails unless every destination has exactly one
driver, each top output is driven, each child input is driven or has an explicit
default, all generated identifiers are injective, and recomputation yields the
same hashes. A receipt is provenance for one emitted artifact, not GHDL or ISA
qualification evidence.

## 7. Current-gap gate

`HwScalarRuntimePipelineV5Direct` now owns the ordered public ABI and complete
direct binding graph in its structural identity. It validates every recorded
endpoint direction, width, and single destination driver, every child input,
and every top output; the public ABI deliberately contains no promoted
child-private port.

The router now owns the `sticky_fault` inhibit and class-ready inputs; the
direct map binds fault-owner feedback once per destination, pending busy,
stateful completion-ready returns, typed illegal-context zeroes, the shared
merge admission ready to all four class-ready inputs, and router-ready back to
the decoded-uop skid. The typed selector-v5, raw input-valid fault-gate
contract, and disabled MulDiv/CSR defaults are materialized. Remaining work is
the renderer receipt, backend emission, clocked evidence, and qualification.
Construction success and binding hash stability prove graph closure, but not
rendered RTL or executable ISA evidence.

The direct graph intentionally leaves three child outputs unconsumed:
`selector.uop_ready` (router is the sole decoded-uop-ready owner),
`pending.uop_ready` (router uses dispatch readiness, not the owner's legacy
alias), and the completion-skid acceptance/decode-valid audit outputs. They are
not public ABI signals and do not participate in architectural state changes.
