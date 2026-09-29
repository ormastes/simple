# RISC-V scalar runtime pipeline v5 binding plan

## Status

V5 currently owns the direct decoder, decoded-uop skid, immediate leaves,
pending/LSU/fence leaves, completion merge, completion skid, and global fault
owner/gate constructors.  It intentionally exposes no composition binding map.
The former map promoted every otherwise-unwired child port to a top-level port;
that was not an ABI and could not establish ordered product semantics.

## Required implementation boundary

The replacement composition may expose only this top ABI. `X` is fixed XLEN,
`PA` is physical-address width, and `MASK` is the LSU byte-mask width.

| Direction | Exact ports |
|---|---|
| Input | `clk:1`, `rst:1`, `in_valid:1`, `instruction:32`, `instruction_length_bytes:3`, `rs1_value:X`, `rs2_value:X`, `pc_before:X`, `fallthrough_pc:X`, `privilege:2`, `provider_event_id:64`, `decode_event_id:64`, `completion_ready:1` |
| Memory input | `bus_request_ready:1`, `bus_response_valid:1`, `bus_response_id:64`, `bus_response_data:X`, `bus_response_fault:1`, `bus_response_cause:X`, `bus_response_tval:X` |
| Fence input | `fence_effect_ready:1` |
| Completion output | `completion_valid:1`, every frozen `HwScalarCompletionInterface` field, `runtime_protocol_fault:1` |
| Memory output | `bus_request_valid:1`, `bus_request_id:64`, `bus_request_address:PA`, `bus_request_write:1`, `bus_request_byte_mask:MASK`, `bus_request_write_data:X`, `bus_response_ready:1` |
| Fence output | `fence_effect_valid:1`, `fence_effect_kind:2`, `fence_effect_fm:4`, `fence_effect_pred:4`, `fence_effect_succ:4` |

No child-private ready, accept, fault, selector, decoder, or pending-tag port
is a top-level ABI port. The constructor rejects every promoted endpoint.

Every link has a known source/destination direction and equal width. The
implementation expands each frozen field list one-for-one and rejects
omissions or aliases.

| Order | Required source-to-destination links |
|---|---|
| Decode | `composition.instruction -> decoder.instruction`; every decoder output -> matching `uop_skid.upstream_*`; every top context input -> matching `uop_skid.upstream_*`; `composition.in_valid -> uop_skid.upstream_valid` |
| Router | held skid controls + `pending.dispatch_ready` + `fault_owner.protocol_fault` -> router; router exact immediate/pending valid/tag/ready -> immediate adapter, selector, pending, and `uop_skid.uop_ready` |
| Immediate | held uop payload -> ALU/control/system/illegal; router lane valids -> adapter; adapter immediate valid -> selector `uop_valid`; all four provider valid/fault/full envelopes -> selector; selector ready <- merge immediate-ready |
| Stateful | pending request fields -> LSU projection/owner and FENCE; projection -> LSU; pending completion-ready -> selected provider; provider ready/accept, control IDs, full envelope, fault -> matching pending fields; MulDiv/CSR inputs are typed zeros only |
| Merge/skid | selector + pending full envelopes -> merge; `completion_skid.upstream_ready -> merge.skid_upstream_ready`; merge readies -> selector/pending; merge selected envelope -> skid upstream; top completion-ready -> skid downstream; skid envelope -> top completion fields |
| Effects | raw top bus/fence inputs -> gate provider-facing inputs; gated values -> LSU/FENCE; raw LSU request/response-ready and FENCE effect -> gate; gated outputs -> top memory/fence ABI |
| Fault loop | router, adapter, ALU, control, system, illegal, selector, pending, projection, LSU, FENCE, merge, uop skid, and skid faults -> gate raw inputs; `gate.fault_in -> fault_owner.fault_in`; `fault_owner.protocol_fault -> gate.sticky_fault`; gate input-ready and completion-valid qualify the ABI |

Reset clears the uop skid, pending/LSU/FENCE owners, completion skid, and
fault owner. A raw fault is captured by the fault owner on its next edge; until
reset, feedback keeps the gate closed. The router accepts no uop while pending
is non-idle. The completion skid is the only top-level completion holder.

The constructor must build that ordered list directly (not infer it from child
port enumeration), validate it before publishing, and include it in canonical
structural identity. Tests must assert required links, forbidden promoted
links, direction/width closure, unknown-endpoint rejection, and canonical
mutation rejection.

## Release and qualification sequence

1. Focused constructor evidence for required/forbidden links, class ownership,
   ready feedback, and sticky-fault lifetime.
2. Dedicated v5 strict renderer with injective identifiers, canonical child
   receipts, total driver closure, and route-specific rejection.
3. RV32/RV64 GHDL analyze/elaborate, then a clocked ALU → LSU → FENCE scenario
   for stateful latency, bus/effect backpressure, completion holding, fault,
   reset, and no overtaking.
4. With an admitted pure-Simple CLI: focused specs once, changed-file lint and
   duplicate checks, then compiler/core qualification. The Rust seed and stale
   deployed runner are not qualification.
