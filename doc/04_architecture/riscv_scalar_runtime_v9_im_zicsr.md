<!-- codex-architecture -->
# Runtime scalar pipeline V9: combined IM, Zicsr, and Zifencei

## Status

Implemented source-level product; production qualification remains blocked.
V9 is a new versioned product, not a change to V7 IM or V8 Zmmul+CSR. It has
no release claim and must not be released from bootstrap-seed evidence.

## Decision

V9 accepts exactly `rv32im_zicsr_zifencei` and
`rv64im_zicsr_zifencei`. Each is one canonical ordered decoder plan: base I,
the complete M extension, Zicsr, then Zifencei. The constructor rejects V7
IM-only, V8 Zmmul+CSR, standalone Zicsr, Zmmul-only, and compatible-looking
reordered/receipt-mismatched plans. A V9 decoder plan must expose M as class
4/effect 0/tag 2 and CSR as class 6/effect 3/tag 3.

V9 is a direct, flattened composition with exactly 21 compiler-owned children:

```
decoder, uop_skid, alu, control, system, illegal_provider,
router_v9, immediate_adapter, pending, projection, lsu,
m_provider, csr_provider, fence, selector, completion_merge,
completion_skid, global_fault_gate_v9, fault_owner, defaults, zero_defaults
```

There is exactly one stateful tag-2 `strict_riscv_scalar_runtime_m_provider`
and one stateful tag-3 `strict_riscv_scalar_runtime_csr_provider`. The former
is the V7 flat unified IM owner; the latter is the V8 flat CSR owner. Neither
is wrapped, duplicated, substituted with V6’s Zmmul provider, nor composed as
a sequential child of another provider. All other pending tags retain their
existing sole provider and retire through the existing completion merge/skid.

## Ownership and service boundary

`pending` dispatches one registered decoded uop to exactly one tag. Tag 2 and
tag 3 each receive the complete pending request envelope and each return the
same 25-field held scalar completion ABI: valid, tag, architectural writeback,
identity/instruction/PC/fallthrough, privilege/event/lineage, memory, trap,
and redirect fields. The completion is stable until its unique
`completion_valid && completion_ready` consume edge; an owner never rereads
live request inputs while busy or held.

The M owner exposes only `request_*`, `completion_*`, and
`provider_protocol_fault`. It accepts all RV32IM M rows and RV64IM adds the
five W rows, using separate 64-bit and 32-bit divider state. The CSR owner
adds V8’s frozen synchronous-service ABI: `csr_lookup_valid`, 12-bit
`csr_lookup_address`, `csr_lookup_read_enable`, `csr_present`, XLEN
`csr_read_value`, and held-consume `csr_commit_valid/address/value`. CSR
lookup data and policy/write intent are captured at request acceptance;
`csr_commit_valid` is legal intent AND completion consume, thus exact once
under backpressure. No V9 service multiplexes or aliases tag-2 and tag-3
state.

## Fault containment

V9 owns a versioned 12-source fail-closed gate. Its ordered sources are
`router_fault`, `decoded_uop_skid_fault`, `adapter_fault`, `selector_fault`,
`pending_fault`, `projection_fault`, `m_fault`, `csr_fault`, `lsu_fault`,
`fence_fault`, `merge_fault`, and `completion_skid_fault`, plus the existing
sticky fault-owner feedback. Any source blocks input acceptance, completion
retirement, LSU/fence effects, and CSR lookup/read-enable/commit. A malformed
tag-2 or tag-3 handshake latches only its provider fault and produces no
completion or service side effect. CSR policy failures are admitted execute
traps, not protocol faults.

## Acceptance boundary

`REQ-G2-012` covers the unique pending/completion/fault ownership;
`REQ-G2-013` covers exact full-M rows; `REQ-G2-016` covers exact Zicsr rows and
service behavior; `REQ-G2-017` covers the typed FENCE/FENCE.I accepted-effect
owner and the explicit Zifencei profile gate (with direct behavioral evidence
owned by the standalone FENCE scenarios); `NFR-G2-003` covers elaboration-time
RV32/RV64 and stable strict lowering. Source topology is insufficient: acceptance requires one
admitted self-hosted runtime execution of structural, clocked full-pipeline
GHDL, and required generated-RTL formal/RVFI readiness gates. Bootstrap seed
or a source-only diagnostic cannot establish qualification.

## Formal/RVFI boundary

V9 formalization is a separate versioned wrapper over the canonical rendered
V9 entity, never another execution datapath. The wrapper captures input
instruction and source-register evidence on `in_valid && in_ready`, assigns a
monotonic retirement order to that accepted one-entry transaction, and holds
the evidence until `completion_valid`. It maps completion identity, PC,
writeback, memory, privilege, and the OR of execute/memory traps to standard
RVFI outputs. RVFI interrupt is explicitly **unsupported** in this product;
the V9 formal contract must state that scope exclusion rather than claim an
unimplemented interrupt source. CSR lookup/commit and FENCE effects require
separate exact-once properties because base RVFI does not encode them.

The wrapper exports fault, CSR-commit, and FENCE-effect observer qualifiers to
the V9 formal harness. This keeps those non-RVFI effects observable without
changing the frozen pipeline ABI. The formal artifact generator and strict
receipt reducer are versioned alongside the wrapper; the legacy RV32 ADD
formal aggregate cannot consume their receipts.
