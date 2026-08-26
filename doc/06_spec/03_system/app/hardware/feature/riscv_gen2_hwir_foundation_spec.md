# RISC-V Gen2 HWIR Foundation

## Purpose

This scenario verifies that a minimal Gen2 hardware product selects its XLEN
at elaboration time, lowers through the strict typed HWIR boundary, and emits a
non-empty VHDL module without invoking the legacy VHDL route.

No self-hosted qualification receipt exists at this revision. The planned
qualification writer, not this manual or a bootstrap-seed scenario run, must
write the RV32/RV64 GHDL receipt set under the retention policy in the system
test plan before any qualification claim is made.

Every GHDL “proves”, “covers”, or “simulates” statement below describes a
required planned qualification scenario, not completed self-hosted evidence.

## Scenarios

1. Create an RV32 product with two `Bits[32]` inputs and one output; verify
   strict lowering and VHDL emission succeed, the width is concrete, and the
   result cannot use legacy fallback.
2. Supply an invalid product configuration; verify lowering rejects it with the
   stable XLEN diagnostic and still cannot use legacy fallback.
2a. Exercise the fixed-width critical compressed boundary with a legal
   C.EBREAK parcel and illegal zero parcel, then derive the non-advertising
   25-entry capability manifest from the declarative ISA table. This is
   compiler-host evidence only: it does not advertise full Zca or claim
   target-RTL equivalence.
3. Construct typed parcel extraction and C.EBREAK equality/select graphs;
   analyze and simulate the emitted VHDL with GHDL, including both C.EBREAK
   match and non-match outputs.
4. Unit-level real-MIR extraction accepts the exact frontend-shaped C.EBREAK
   conditional CFG and rejects an altered branch edge before emission.
5. Build the typed C.J predecode graph for a critical RV32 product; analyze and
   simulate positive, negative, and non-row parcels, verifying canonical JAL,
   original two-byte length, redirect validity, target, and fallthrough PC.
6. Build C.BEQZ and C.BNEZ branch-predecode graphs for critical RV32 and RV64
   products; simulate taken and untaken explicit-register conditions, positive
   and negative offsets, and cross-row parcels. Verify XLEN and physical-address
   widths are concrete in each emitted module and nonmatching rows fail closed.
   Bind `rs1_index = 01000` for compressed x8 and prove a mismatched x9 index
   suppresses legality, canonical instruction output, and redirect.
7. Build one flattened C.J/C.BEQZ/C.BNEZ control-predecode module through the
   public strict product route for critical RV32 and RV64 products. Assert its
   `hwir-gen2-product` route, stable module node, concrete XLEN, and critical
   configuration profile before GHDL proves direct-jump, zero/nonzero branch,
   mismatched-register-index, and unsupported-parcel behavior through a single
   emitted module with concrete PA and XLEN widths.
8. Invoke `simple-vhdl` with a Gen2 target outside critical assurance and prove
   it rejects before legacy generation or stale-artifact removal.
9. Invoke the source-less `riscv-gen2-zca-migrating-predecode-v1` product under
   critical RV32-Zca policy; verify VHDL/GHDL output and an honest manifest
   with an empty user source closure. A noncritical request must preserve a
   prior artifact.
10. Emit the one-entry RV32/RV64 stateful parcel frontend only from a typed
    sequential plan that owns registers, reset, transitions, decoder pins, and
    output bindings. Verify its strict route and closure bind the complete
    configuration, port contract, ordered plan, decoder identity/digest, and
    origins; malformed plans reject before artifact replacement.
11. Normalize C.ADDI4SPN, C.LW, C.SW, and C.LWSP behind explicit outcome contracts.
    GHDL proves the reserved C.ADDI4SPN zero immediate is illegal and proves
    C.LW/C.SW matching versus nonmatching classifiers and C.LWSP's reserved
    register rejection without using a canonical-word sentinel as a predicate.
12. Compose admitted outcomes with C.J/C.BEQZ/C.BNEZ and typed C.JR/C.JALR
    redirects into one strict-HWIR migrating decoder. GHDL proves C.LW,
    positive C.ADDI16SP, aligned C.JR/C.JALR redirects, mismatched-index
    rejection, and reserved-zero C.ADDI16SP illegal fallthrough; the one-entry
    product instantiates this decoder.
13. Emit the versioned v2 C.EBREAK frontend under critical policy only from its
    typed sequential graph and complete graph-hash closure. Exercise two clean
    consecutive one-entry transactions with incrementing 64-bit lineage,
    issued backpressure, early/stale/mismatched/repeated retirement faults,
    stale-effect suppression, terminal-lineage no-wrap faulting, and reset
    recovery/retirement priority;
    malformed closure inputs preserve a prior artifact and produce no manifest.
14. Compare the v1/v2 frontend admission lists to the declarative critical-Zca
    capability table. V1 must omit only C.EBREAK; v2 must contain every one of
    the 25 entries exactly once. This catches composition/table drift before
    capability metadata can be widened.
15. Emit the isolated RV32 C.JAL row and prove positive/negative J-immediate
    redirects plus canonical `JAL x1`; the common profile must reject it, then
    compose it only in the dedicated RV32 C.JAL migrating decoder because its
    corresponding RV64 parcel class is C.ADDIW.

16. Emit the reciprocal isolated RV64 C.ADDIW row and prove its signed
    immediate canonical form plus reserved `rd=x0` rejection. Its product is
    distinct from RV32 C.JAL and remains frontend-predecode-only.

17. **REQ-G2-009, REQ-G2-010, NFR-G2-010, NFR-G2-011 — RV32 C.JAL v3 product.**
    1. Under critical policy, emit the source-less v3 trap product only for
       `rv32-zca-cjal-critical`.
    2. Check its dedicated C.JAL frontend entity, empty source closure,
       concrete RISC-V 32 target/profile, C.JAL admission, and incomplete
       target-evidence manifest marker.

18. **REQ-G2-009, REQ-G2-010, NFR-G2-010, NFR-G2-011 — RV64 C.ADDIW v3 product.**
    1. Under critical policy, emit the source-less v3 trap product only for
       `rv64-zca-addiw-critical`.
    2. Check its dedicated C.ADDIW frontend entity, empty source closure,
       concrete RISC-V 64 target/profile, admitted RV64 Zca rows, exclusion of
       C.JAL, and incomplete target-evidence manifest marker.

19. **REQ-G2-002, REQ-G2-010, REQ-G2-011, NFR-G2-010, NFR-G2-012 — RV64
    conditional decoder vector.**
    1. Compile the RV64 C.ADDIW mission-critical trap frontend and confirm the
       complete 32-row overlap closure is present.
    2. When GHDL is available, analyze, elaborate, and run the exact RV64
       decoder vector testbench; otherwise retain this as a required planned
       qualification scenario rather than target evidence.

20. **REQ-G2-003, REQ-G2-005, REQ-G2-009, REQ-G2-010, NFR-G2-010,
    NFR-G2-011 — rejection and stale-artifact preservation.**
    1. Reject a wrong RV32 C.JAL target and a noncritical RV64 C.ADDIW request
       before either can replace a retained artifact or create a manifest.
    2. Reject the retired v2 trap identity, a noncritical compiler-owned
       product, and unsupported critical hardware before VHDL/manifest output
       exists; each path preserves its prior artifact.

## Requirement traceability

- REQ-G2-001..005: first scenario.
- NFR-G2-001..003: deterministic rejection and no-runtime-selection behavior.
- NFR-G2-004: the typed parcel-mask scenario supplies `HwConstant` and
  `HwCombOp` operands to the renderer rather than VHDL fragments; focused
  source-ownership lint remains the global ownership gate.
- NFR-G2-005: the strict-RV32 scenario proves the generated result cannot
  select legacy fallback; focused route/source review keeps V1 explicit.
- REQ-G2-007/NFR-G2-007: the shared compressed hardware subset carries only
  fixed-width parcel/canonical data and reason codes. Its zero, reserved, and
  RV32-C.JAL/RV64-C.ADDIW divergent cases remain explicit non-legacy paths.
- REQ-G2-008/NFR-G2-009: the declarative 25-entry critical subset derives a
  non-advertising host-side capability manifest; it records incomplete
  target-RTL evidence rather than claiming Zca or a release profile.
- NFR-G2-008: the mission-critical C.EBREAK graph uses fixed-width typed
  values, rejects an invalid predicate before emission, and has no legacy
  decoder path.
- REQ-G2-003/004: the C.J scenario specifies target simulation through the
  frozen predecode interface; source/spec evidence also checks admission only
  through its aggregate real-MIR shape. A retained self-hosted GHDL receipt is
  still required before this becomes row-level target capability evidence.
- REQ-G2-003/004: C.BEQZ/C.BNEZ target vectors use the frozen branch-predecode
  interface and its explicit `rs1_index: Bits[5]` plus `rs1_value: Bits[XLEN]`
  binding. This scenario
  is specified to prove RV32/RV64 taken, untaken, `+2`, `-2`, sign-sensitive
  `-256`, and cross-row and mismatched-index fail-closed behavior. Until its
  receipt exists, these are planned target vectors, not row-level target
  capability, full-Zca, or release evidence.
- REQ-G2-003/004: the public control-predecode product emits one flattened
  module for RV32 and RV64 and reports strict route/node/profile/XLEN
  provenance before the planned target simulation. Source/spec evidence covers
  the bounded stateless three-row shape; it is not target evidence, a full
  frontend, parcel buffer, dispatch channel, or retirement proof.
- REQ-G2-006: a noncritical `--riscv-gen2-target` request is rejected before it
  can take the legacy route or replace a pre-existing artifact.
- NFR-G2-006: compiler-owned Gen2 artifacts retain the canonical critical
  assurance-policy snapshot and policy hash captured by the compile context;
  validation rejects a missing, noncanonical, or noncritical snapshot before
  the VHDL bundle is persisted.
- REQ-G2-009/NFR-G2-010: the compiler-owned migrating product accepts only the
  concrete critical Zca target, emits distinct `hwir-gen2-product` provenance
  with no fabricated user source closure, and rejects before cleanup when
  policy is noncritical. The legacy three-row product identity remains separate.
- REQ-G2-010/NFR-G2-011: stateful parcel emission derives only from a typed
  sequential plan: registers, reset values, priority guards, assignments,
  decoder pins, and output bindings. Both RV32 and RV64 record a nonempty
  decoder-closure graph hash and have no legacy fallback.
- REQ-G2-010/NFR-G2-011: the RV32 and RV64 trap-frontend scenarios require
  precise C.EBREAK visibility, issued-entry backpressure, two consecutive
  matching transactions with incrementing 64-bit lineage,
  early/stale/mismatched/repeated-retirement sticky-fault containment, fetch
  refusal while faulted, suppressed stale trap effects, and reset-only recovery
  including same-edge reset/retirement priority. Source/unit specifications
  cover the terminal lineage rule because reaching `2^64-1` is not a practical
  simulation vector; admitted runtime evidence remains pending.
- REQ-G2-011/NFR-G2-012: normal-row outcomes use explicit classifier/reserved
  predicates and fixed predecode metadata. Planned GHDL vectors cover
  C.ADDI4SPN, C.LW, C.SW, and C.LWSP, while the unit specification describes
  the whole admitted tranche. Rows with reserved, redirect, or trap semantics
  remain outside composition; neither source artifact is a retained receipt.
- REQ-G2-010/NFR-G2-011: the versioned C.EBREAK trap product is emitted through the
  same typed sequential plan and records a nonempty compiler-product graph
  hash. The v1 decoder ISA composition remains unchanged; stateful products
  remain development-stage ABI/version decisions until the self-hosted writer
  creates a planned qualification receipt.
- REQ-G2-011: frontend admission is closed against the declarative capability
  table. This is a structural provenance guard, not full generated-RTL
  equivalence.
- REQ-G2-011: the RV32 C.JAL specification has a strict-row contract, planned
  GHDL vectors, an explicit common-profile rejection, and a separate RV32-only
  migrating product. It remains outside the shared RV32/RV64 capability claim,
  and target evidence awaits the retained receipt.
- NFR-G2-012: RV64 C.ADDIW has the reciprocal source/spec contract, planned
  GHDL vectors, and a separate `rv64i_zca` product closure. It is not target
  evidence or evidence of a complete RV64 scalar core or profile compliance.
- REQ-G2-011/NFR-G2-012: the migrating v1 predecode composes the admitted
  outcome tranche with the branch-control slice using explicit `legal` priority
  only. It remains bounded and does not claim full-table equivalence.

## Scope note

This executable scenario defines strict VHDL CLI gates, bounded stateless
control composition, and development-stage typed stateful C.EBREAK handling.
It is not a full Gen2 frontend, complete trap controller, or protected-core
equivalence claim. The current self-hosted `simple-vhdl` must still run the
RV32/RV64 product routes before release evidence can be claimed.
