<!-- codex-design -->
# Runtime scalar pipeline V7: full dynamic IM detail design

## Scope

V7 is the complete dynamic scalar M lane for `rv32im` and `rv64im`. It replaces
the V6 Zmmul multiply-only tag-2 provider with one flattened
`runtime_m_provider`; it does not alter V8 CSR, add class 6/tag 3, or claim a
combined IM+Zicsr product.

## Implementation status

The source-level owner, router, direct pipeline, strict VHDL renderer, unit
specs, provider GHDL spec, system structural spec, and manual are present.
This design records their intended topology, not a qualification PASS. The
deployed release-path executable identifies itself as the Rust bootstrap seed,
so it cannot qualify any V7 scenario. No admitted full-pipeline clocked GHDL
or generated-RTL formal/RVFI evidence exists.

## Interface and admission

The provider retains the V6 tag-2 request/completion ABI and the complete
25-field scalar completion envelope. The implemented port names are
`request_*`, `completion_*`, and `provider_protocol_fault`; no V7-specific
`setup_runtime_m_owner`/`offer_runtime_m_request`/`expect_runtime_m_completion`
SPipe helper contract exists.

`request_ready = !busy_reg && !completion_valid_reg && !fault_reg`; acceptance
requires request valid, ready, and the full contract predicate. The predicate
combines exact `RiscvScalarRuntimeDivAdmissionContract` plan hash/profile with
tag 2, legal decoder state, class/effect/memory, row/semantic/form/width,
raw rd/rs1/rs2 binding, original/canonical identity, length 4, PC/fallthrough,
lineage, and equal dispatch/decode event IDs. `row_matched` from the
normalizer is never treated as admission by itself.

Malformed offered tag-2 traffic when ready captures only sticky protocol-fault
state. It neither starts datapath state nor emits a completion. Ordinary offer
backpressure while ready is low is not a fault.

## Datapath schedule

At capture, normalize x0 sources, latch all metadata, clear inactive state,
and select exactly one operation family. Multiply follows the V6 add/shift
schedule for MUL/MULH/MULHSU/MULHU/MULW. Divide/remainder uses restoring
iterations from the selected fixed geometry:

1. Shift next dividend bit into the `(W+1)` remainder candidate.
2. Compare candidate remainder to the zero-extended divisor.
3. Subtract and append quotient bit when the comparison succeeds.
4. Increment count and finalize only after `count == W`.

For signed operations, capture absolute magnitudes and result sign controls;
negate quotient/remainder after unsigned restoration as required. DIV/DIVU
select quotient and REM/REMU select remainder. Divisor zero and signed-minimum
over minus one bypass iterations to the captured architectural result. RV64
uses named `d64_*` and `d32_*` divider state. Every W row consumes low 32 bits
despite hostile upper input bits, then sign-extends its final 32-bit result.

## Flat strict-HWIR owner schedule

`strict_riscv_scalar_runtime_m_provider(module_name, config, plan)` is one
flat `HwSequentialModuleDef` (`child_entity == ""`). The reusable divider is
only a transition-equation reference: it cannot be a child graph. The V6
multiply provider is likewise reference-only. Every signal below has one comb
producer and every register is written by one active rule only.

### Operation map and exact-row construction

The implemented three-bit `operation_reg` distinguishes the multiply family
(`MUL`, `MULH`, `MULHSU`, `MULHU`, `MULW`). A separate `family_div_reg` selects
the division/remainder machinery, whose exact quotient/remainder, signedness,
special-case, and word controls are captured by the namespaced normalizer
state. It does not encode all thirteen rows in `operation_reg`.
Construction accepts exactly 8 M rows for RV32IM or 13 for RV64IM and rejects
all other profiles (including Zmmul and IM+Zicsr). Each required row creates a
local mask/value, semantic opcode, decoder-row index, declared-width constant,
and exactly one `row_<n>_{form,semantic,index,width,candidate,selected}` set.
`selected_any` is their OR and `request_operation` is their matching mux fold.
The constructor verifies the exact `RiscvScalarRuntimeDivAdmissionContract`
structural hash/profile/xlen before forming the module.

### Registers

Common owner state:

| Register | Width | Purpose |
|---|---:|---|
| `busy_reg`, `full_reg`, `fault_reg` | 1 | working / held completion / sticky protocol fault |
| `family_div_reg`, `word_reg` | 1 each | multiply/divide family and RV64 word divider selection |
| `operation_reg` | 3 | captured multiply-family operation |
| `count_reg` | 7 | multiply count |
| `acc_reg`, `multiplicand_reg` | `2*xlen` | product state |
| `multiplier_reg`, `lhs_reg`, `rhs_reg` | `xlen` | product input/correction state |

RV32 owns only the 32-bit `d32_*` divider namespace. RV64 owns both a 64-bit
`d64_*` namespace for XLEN operations and the 32-bit `d32_*` namespace for W
operations. The `d64` namespace is:
`d64_{dividend,quotient,original_dividend}_reg : 64`,
`d64_{divisor,remainder}_reg : 65`, `d64_count_reg : 7`,
`d64_{result_negate,remainder_negate,select_remainder}_reg : 1`, and
`d64_special_reg : 2`.

The `d32` namespace is present for RV32 and RV64:
`d32_{dividend,quotient,original_dividend}_reg : 32`,
`d32_{divisor,remainder}_reg : 33`, `d32_count_reg : 6`,
`d32_{result_negate,remainder_negate,select_remainder}_reg : 1`, and
`d32_special_reg : 2`. In RV64, no `d32_*` signal or register shares a
destination with a `d64_*` one.

Capture all 25 completion fields as `completion_<field>_reg`; on capture,
`completion_rd_write_reg = (instruction_rd_field != 0)`, irrespective of the
result value. Memory/trap/redirect fields are captured zero and all identity,
PC, privilege, and event fields come from the accepted request.

### Admission and capture

`request_ready = !busy_reg && !full_reg && !fault_reg`;
`request_handshake = request_valid && request_ready`. For tag 2 only,
`admission_final` is the named-AND reduction of:

```
decode_legal && !illegal_valid && class_is_4 && memory_effect_is_0 &&
instruction_length_is_4 && original_equals_canonical && lineage_valid &&
provider_event_id_equals_decode_event_id && fallthrough_pc_equals_pc_before_plus_4 &&
canonical_rd_rs1_rs2_equal_raw_fields && selected_any
```

The row term includes encoding, semantic opcode, decoder row index, and
declared width. The normalizer's `row_matched` never authorizes capture.
`malformed_request = request_handshake && tag_ok && !admission_final`; it alone
sets `fault_reg`, without datapath activity or completion. Non-tag-2 traffic
and all traffic while not ready are ignored by this provider.

`effective_rs1` and `effective_rs2` mux source x0 to zero before all math.
Word rows take their low 32 bits. Capture derives absolute magnitudes, quotient
and remainder negate flags, and `special_reg` (`00` normal, `01` divisor zero,
`10` signed min/-1) for the selected width, then clears inactive state. No
live request input is referenced after capture.

### Combinational transition sets

Retain one-producer V6 multiply wires: `multiplier_lsb`, `acc_added`,
`acc_next`, `multiplicand_next`, `multiplier_next`, `count_last_value`, product
slices, signed-high corrections, and `mul_architectural_result`. The final
multiply result is derived from `acc_next`, so it includes the last add.

Inline restoring transition equations under precisely these separate names:

```
d64_dividend_msb, d64_dividend_msb_extended, d64_remainder_shifted,
d64_shifted_remainder, d64_remainder_ge_divisor, d64_remainder_subtracted,
d64_remainder_next, d64_quotient_shifted, d64_quotient_bit_extended,
d64_quotient_next, d64_dividend_next, d64_remainder_next_low,
d64_quotient_next_corrected, d64_remainder_next_corrected,
d64_normal_result_next, d64_special_result, d64_architectural_result_next
```

RV64 adds the identical `d32_*` transition set at widths 32/33 and sign-extends
`d32_special_result` to 64. Each transition shifts in the dividend MSB,
compares/subtracts, then appends the quotient bit. Final correction uses
`*_quotient_next` and `*_remainder_next_low`, never pre-transition registers;
the detached divider leaf would otherwise yield a one-cycle-old result.
Div-zero selects all ones for DIV/DIVU or original dividend for REM/REMU;
signed overflow selects minimum for divide or zero for remainder.

`owner_architectural_result` is one mux controlled by captured `family_reg`:
multiply, d64, or d32 result. It is sampled only in its matching final rule;
there is no runtime-width signal, second tag-2 provider, or dynamic resizer.

### Rule priority (highest first)

1. `reset`: clear every common, d64, d32, and completion register.
2. `protocol_fault`: `fault_any && !fault_reg`; set fault, clear busy/full and
   completion payload; no malformed request is retained.
3. `completion_consume`: `full_reg && completion_ready && !fault_reg`; clear
   full/payload only. A request may arrive on the following cycle, never the
   same edge.
4. `mul_finish`, then `mul_iterate`: `busy && family==0`, final at
   `count_reg == xlen-1`; finish sets full/clears busy and writes only the
   completion result, iterate writes only multiply progression/count.
5. `d64_finish`, then `d64_iterate`: `busy && family==1`, final at
   `d64_count_reg == xlen-1`; only `d64_*` progression is written while active.
6. RV64 `d32_finish`, then `d32_iterate`: `busy && family==2`, final at
   `d32_count_reg == 31`; only `d32_*` progression is written while active.
7. `request_capture`: `request_handshake && tag_ok && admission_final`; latch
   all metadata, select exactly one family, initialize its state, clear the
   inactive namespaces, and set busy.

Special divisions follow their selected geometry's fixed iteration count. This
keeps normal and exceptional requests indistinguishable at the ready/valid
boundary while preserving a fixed register producer set.

## Completion and fault behavior

On normal finalization, the provider creates one completion with tag two,
captured IDs/instruction/PC metadata, zero memory, trap, and redirect effects,
and `rd_write = (rd != 0)`. It holds every field unchanged until the single
completion consume edge, then becomes eligible for a request on the following
cycle. Reset clears busy, completion, fault, all datapath, and metadata state.

V7 currently reuses `strict_riscv_scalar_runtime_global_fault_gate_v6`; the
pipeline binds the unified M provider's one `provider_protocol_fault` output
to its `muldiv_fault` input. There is no second M fault source.

## Implementation constraints

- Build one `HwSequentialModuleDef` graph, with unique signal producers and
  explicit fixed-width operations; do not create a child sequential divider.
- Keep RV64 `d64_*` and `d32_*` state disjoint; do not dynamically resize a
  divider or reuse XLEN state for W rows.
- Preserve the V6 public pipeline ABI in V7 versioned files, then lower only
  through the V7 strict backend renderer.
- Fail closed on unavailable HWIR primitives or invalid metadata. No raw VHDL
  arithmetic snippets, host-computed dynamic results, runtime provider mux,
  or raw-source fallback is permitted.

## Evidence hooks and open qualification work

Current source-level coverage is in
`test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_m_provider_spec.spl`,
`test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_pipeline_v7_flat_spec.spl`,
`test/01_unit/compiler/backend/riscv_scalar_runtime_pipeline_v7_flat_to_vhdl_spec.spl`,
and `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v7_im_spec.spl`.
The provider GHDL source is
`test/02_integration/compiler/riscv_scalar_runtime_m_provider_ghdl_spec.spl`.
It includes reset/backpressure/fault behavior, but not RV32 multiply vectors
or whole-pipeline simulation. Those, an admitted self-hosted run, and formal
RTL readiness are required before the design can be marked qualified.
