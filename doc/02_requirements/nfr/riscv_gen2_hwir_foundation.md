# RISC-V Gen2 HWIR Foundation — NFR Requirements

- NFR-G2-001: Equal valid inputs produce byte-identical VHDL and stable IDs.
- NFR-G2-002: Invalid or unsupported input produces a stable, actionable
  diagnostic; it never produces placeholder RTL or a fallback result.
- NFR-G2-003: RV32/RV64 choice is elaboration-time data; emitted modules contain
  only the selected concrete width and no XLEN-selection signal/multiplexer.
- NFR-G2-004: New Gen2 semantics contain no raw VHDL string fragments outside
  the typed emitter owner.
- NFR-G2-005: Existing V1 generators remain untouched and reachable only by
  their explicit legacy caller.
- NFR-G2-006: Critical-profile hardware-tagged Gen2 products use the typed,
  snapshot assurance policy at the production VHDL boundary, require an
  explicit RV32/RV64 target, and fail closed rather than reaching legacy VHDL.
- NFR-G2-007: Shared compressed semantics used by `@hardware` adapters carry
  only fixed-width data and reason codes; text diagnostics and XLEN-dependent
  classification remain outside the emitted hardware interface. Synthesizable
  immediate and instruction-assembly intermediates use explicit `u32`
  two's-complement values rather than signed host-width values.
- NFR-G2-008: A mission-critical compressed path must use a separate,
  fail-closed subset entrypoint with no legacy fallback, runtime XLEN/config
  input, provider lookup, or text-valued hardware state. Every 16-bit parcel
  is deterministically classified by an exhaustive test before use.
- NFR-G2-009: A partial critical compressed implementation must carry a
  host-side capability manifest that forbids advertising full Zca and records
  outstanding target-RTL equivalence before release.
- NFR-G2-010: A compiler-owned product has deterministic compiler provenance,
  concrete RV32/RV64 target/profile and typed HWIR node identity, but never a
  fabricated source file, source span, or legacy source-catalog route.
- NFR-G2-011: The first sequential Gen2 lane uses one named synchronous
  active-high reset domain, explicit typed state/register widths, stable
  payload while dispatch is stalled, and no hidden legacy PC, register-file,
  or retirement owner.
- NFR-G2-012: Composed compressed decode has deterministic table order and an
  explicit legal/match signal per row. It must reject overlapping or unproven
  row admission rather than using canonical-zero inference.
- NFR-G2-013: Every scalar provider boundary is fail-closed under forged
  instruction/register/provider identity, invalid ready/valid ordering, stale
  response identity, and child-graph substitution. Invalid or stalled payloads
  are stable and normalized; sticky protocol faults are externally observable.
- NFR-G2-014: M/Zmmul arithmetic uses one width-parameterized semantic source,
  with deterministic structural identity and no host-width shortcut that can
  change unsigned 64-bit, signed-high, division corner, or RV64 W behavior.
- NFR-G2-015: System exception projection is deterministic and fail-closed:
  invalid input normalizes every payload field, the concrete instruction and
  privilege-derived cause are part of the typed graph receipt, and no system
  provider may bypass the completion skid, trap normalizer, fault aggregator,
  or sole retirement owner.
- NFR-G2-016: Scalar-I arithmetic remains one monomorphized RV32/RV64 graph
  family. Shift serialization must never convert an arbitrary XLEN-wide value
  directly to VHDL INTEGER; out-of-range counts have defined typed behavior,
  and no emitted graph contains runtime opcode, extension, or XLEN selection.
- NFR-G2-017: CSR access is elaboration-time specialized and fail-closed. No
  emitted graph contains runtime extension/provider selection, no denied access
  asserts a CSR read or write effect, and a missing atomic CSR state owner must
  remain an explicit qualification blocker rather than being represented as a
  successful Zicsr product.
- NFR-G2-018: Fence effects are explicit, deterministic, and atomic with the
  accepted scalar event. A product must never lower a fence to a no-op, retire
  it before effect acknowledgement, duplicate it while stalled, or admit a
  future `memory-order` row as FENCE without an exact ISA identity contract.

Evidence is implemented as focused unit and system scenarios,
deterministic-render comparison, strict-route provenance/fail-closed tests,
RV32/RV64 adapter vectors, and focused lint/duplication gates with
`SIMPLE_SAFETY_PROFILE=critical`.  A scenario or bootstrap-seed run is not a
qualification receipt: release evidence additionally requires the current
self-hosted compiler, the RV32/RV64 generated-VHDL/GHDL route, and the
maintenance gates recorded in the system test plan.

## Coverage contract

For compiler-owned Gen2 HWIR/product/provenance changes, the qualified
self-hosted run must report at least **80% branch coverage** across the changed
owned `.spl` modules and their directly corresponding focused tests. The
denominator comes from a compiler-time, zero-count semantic decision inventory;
runtime outcomes are left-joined by stable file/span identity, so an unexecuted
decision cannot disappear. Generated VHDL, testbench literals, legacy V1
generators, and the separate architectural-retirement producer are the exact
four exclusions; unavailable GHDL tooling is a blocker, never an exclusion. The
qualification receipt records the coverage command, report location, measured
percentage, an authoritative source-hash-bound owned-file list (including
explicit empty/deleted-file handling), and each exclusion. The authoritative
list is an ordered, duplicate-free part of the admitted runner source revision;
it is never inferred from a Git revision range. A retained canonical
`sha256<two spaces>path` manifest binds every source independently, and all
paths and hashes are revalidated immediately before the receipt composer runs.
Every listed path must remain a nonempty, regular, non-symlinked `.spl` file. A
missing, deleted, empty, symlinked, or changed entry blocks qualification until
ownership and this requirement are reviewed together; it cannot become an
implicit exclusion. A bootstrap-seed test run does not satisfy this contract.
Qualification runs on Linux with GNU
Coreutils `sha256sum` and `timeout`; another host requires a separately selected
and tested portability contract rather than silently changing hashing, timeout,
or canonical-path semantics. The scope excludes unrelated scalar-core,
formal-verification, SimpleOS, database, web, and integration-lane files even
when they share Git history with A13/A14. It includes the complete typed
sequential/parcel/trap dependency closure, qualification composer, compiler
coverage inventory path, and their directly executed focused specifications.

## Related artifacts

- Feature requirements: `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- Qualification test plan: `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- Parallel execution plan: `doc/03_plan/agent_tasks/riscv_gen2_hwir_foundation.md`
- Architecture: `doc/04_architecture/riscv_gen2_hwir_foundation.md`
- Detail design: `doc/05_design/riscv_gen2_hwir_foundation.md`
- Qualification receipt manual:
  `doc/06_spec/01_unit/app/riscv_gen2_qualification_receipt_spec.md`
- SPipe state: `.spipe/riscv_gen2_hwir_foundation/state.md`
