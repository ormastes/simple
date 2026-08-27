<!-- codex-design -->
# Runtime scalar pipeline V9: IM + Zicsr detail design

## Construction contract

Implement `strict_riscv_scalar_runtime_pipeline_v9_flat` and its sole strict
VHDL renderer for the exact profiles `rv32im_zicsr_zifencei` and
`rv64im_zicsr_zifencei`. The plan receipt/hash, profile text, XLEN, ordered
rows, class/effect codes, and declared widths are construction invariants.
V9 is not a profile flag added to V7 or V8; all public types, router, fault
gate, pipeline, backend, tests, and docs are V9-versioned.

The direct-child list and order are the 21 entries defined by the V9
architecture document. `local_diagnostic`, structural hash, canonical rebuild,
binding closure, and backend rendering must all enumerate that same list.
Every child input and top-level output has exactly one typed binding. No
sequential child graph may be used to glue the M or CSR owners together.

## Router and pending bindings

`strict_riscv_scalar_runtime_class_router_v9` accepts only canonical V9 plans.
It sends M class 4/effect 0 work to pending tag 2 and CSR class 6/effect 3
work to pending tag 3; it rejects class/effect aliases and every non-V9
profile. `pending` retains one dispatch record and must bind the full request
envelope, including raw fields, original/canonical instruction identity,
length, PCs/fallthrough, privilege, lineage, and equal provider/decode event
IDs, to both provider port families.

For tag 2, bind `pending.muldiv_request_*` to the M owner (the historical
pending prefix may remain only if the exact V9 binding table documents it).
For tag 3, bind `pending.csr_request_*` to the CSR owner, wire CSR service
ports from the composition, and bind both held completion envelopes back to
their distinct pending slots. Each provider gets its own completion-ready;
neither is derived from the other provider’s valid or ready signal.

## Provider acceptance and temporal rules

The M owner preserves V7’s complete plan-bound admission, x0 source
normalization, `rd != 0` write suppression, 32/64 divider separation, and
architectural DIV/REM special results. The CSR owner preserves V8’s exact six
forms, captured lookup value/policy, and retirement-gated exact-once commit.
For both owners:

1. `request_ready` is true only while empty, healthy, and not holding a result.
2. Capture requires `request_valid && request_ready` and full exact admission.
3. A malformed offered request latches sticky provider fault, with no result.
4. Normal completion payload is entirely captured/stable through backpressure.
5. Reset clears state, completion, service intent, and fault state.

Rule priority is reset, provider protocol fault, completion consume, active
operation finish/iterate, then request capture. CSR has no deferred lookup
state in V9; its frozen service data is captured on acceptance. M and CSR may
not share an active, full, count, commit, or fault register.

## Global fault and backend

`strict_riscv_scalar_runtime_global_fault_gate_v9` has the 12 named sources
in the architecture document. It gates raw input, completion, bus/fence, and
all CSR side-effect signals. Bind `m_provider.provider_protocol_fault` only to
`m_fault` and `csr_provider.provider_protocol_fault` only to `csr_fault`.
The old V8 `muldiv_fault` name must not conceal the V9 unified-M owner.

`strict_riscv_scalar_runtime_pipeline_v9_flat_to_vhdl` is the only lowering
route. It emits one entity containing 21 direct child instances and no V7/V8
wrapper instance. VHDL output must retain separate tag-2/tag-3 ready/valid,
full completion routes, all CSR ports, and the 12 gate inputs. Repeated strict
lowering of one configuration must produce equal receipt and VHDL text.

## Test-facing interface names

Use these future SSpec helpers consistently:

```
setup_v9_runtime_pipeline(profile)
offer_v9_pending_uop(...)
drive_v9_csr_service(present, read_value)
hold_v9_completion_backpressure()
consume_v9_completion_once()
expect_v9_completion(...)
expect_v9_csr_commit_once(...)
expect_v9_protocol_fault_no_effects()
```

The V9 structural and clocked scenarios are implemented. New scenario helpers
must still fail explicitly with `fail(...)` until they acquire a concrete
binding; no no-op scaffolding may count as coverage. The test design uses
`step("...")` rather than legacy Given/When/Then naming.

## RVFI/formal projection

`compile_strict_riscv_scalar_runtime_pipeline_v9_rvfi` wraps only the
canonical V9 VHDL result. It captures `instruction`, `rs1_value`, and
`rs2_value` at the internally accepted input, extracts the source register
fields, and allocates a monotonic order counter at the same edge. The wrapper
holds exactly one operand record in flight and blocks another pipeline input
until that record reaches completion, preventing a later input from
overwriting RVFI operand provenance. This gate is combinationally safe: V9
`in_ready` derives from registered decode-skid/fault state, never the current
input-valid or instruction payload. At completion it
maps `completion_valid`, original instruction, PC pair, writeback, memory
fields, privilege, and execute-or-memory trap to RVFI. RV32 maps IXL to `01`;
RV64 maps it to `10`. Interrupt is emitted only as the contract's explicit
unsupported zero and is an assumption exclusion, not a supported feature.

Formal artifacts bind the canonical V9 graph hash, VHDL hash, profile, RVFI
contract hash, and every job input/output hash. The versioned bundle app and
`scripts/rtl/run-riscv-scalar-runtime-pipeline-v9-formal.shs` accept only that
sealed manifest and replace it atomically with an evidence receipt after prove,
cover, and mutation jobs. Its GHDL PSL harness constrains reset asserted only
on the first formal cycle and released thereafter, with a reachable-retirement
cover; the sealed current scope is RVFI PC/order/trap/fault only, and the
externally executed cover receipt is required before relying on that witness.
V9 solver jobs must separately extend the contract for M semantics and divide
corners, CSR lookup/capture/commit exact-once and policy traps, FENCE effect
discipline, completion stability, and fault containment.

The currently generated harness asserts non-interrupt retirement, sequential
RVFI ordering, PC/trap observability, fault fail-closed behavior, and that CSR
commit or FENCE effect are externally observable. Its PC+4 assertion applies
only to non-control opcodes; branch, JAL, and JALR retirements need their own
redirect-aware solver properties. CSR commit and FENCE effect precede the
completion-skid retirement boundary, so their exact-once pairing is a temporal
solver property, not a same-cycle RVFI assertion. Broader instruction
semantics, CSR policy matrices, and exhaustive side-effect properties remain
solver-job obligations and must not be inferred from the wrapper or smoke test
alone.
