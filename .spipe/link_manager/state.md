# Feature: link_manager (LINK lane — GraphResolveCore, SMF linker, StyleLinker)

## Raw Request

Implement `doc/03_plan/platform/structural_compute/link_manager_plan.md` via
the SPipe dev flow, checking the GPU parser framework interface and design
details as updated on GitHub first; concrete design and interface first, then
push, then small parallel agents with guides.

## Task Type

Contract freeze + staged implementation (structural-compute LINK lane).

## Refined Goal

Freeze the resolve contract v1 (records, enums, ResolveProfile trait, SMF
stage ids, link.* tags, CPU reference codec, golden vectors), then implement
Phase 1 (CPU GraphResolveCore + SmfLinkProfile, byte-identical to the current
SMF linker) per the plan's wave order.

## Acceptance Criteria

- AC-1: Frozen resolve contract v1 with hand-derived golden vectors and a
  contract spec covering exact bytes, round trip, and total-decoder rejects.
- AC-2: Contract reuses identity/wire/placement_contracts — no parallel
  identity, wire, or receipt types.
- AC-3 (Phase 1, later): GraphResolveCore CPU core + SmfLinkProfile produce
  byte-identical SMF output to the current linker, with StageReceipts.
- AC-4 (later): StyleLinker/WebResourceLinkProfile parity vs current resolver;
  custom-property cycle detection.

## Scope Exclusions

- Spatial layout is not a profile; native ELF/Mach-O/PE stays on native
  linkers (plan §Scope).
- MutationOp wire encoding (MUTATE lane), SmfLinkProfile attribute bit
  assignments, GPU batch layouts — deferred per contract doc §6.

## Cooperative Review

Owners: LINK lane (this feature). Shared interfaces consumed read-only:
`structural/wire.spl`, `structural/identity`, `compute/placement_contracts`.
Shared interface names defined by this lane: `ResolveProfile`, resolve record
types, `SMF_LINK_STAGE_L*`, `LINK_TAG_*`. Any temporary shared helper must
fail explicitly with `assert(false)` or `fail(...)`; silent placeholders are
forbidden.

## Architecture Summary

Module Plan:

| Module | Path | Role | State |
|---|---|---|---|
| resolve_types | src/lib/common/structural/resolve/resolve_types.spl | frozen records/enums/trait/stage ids/tags | frozen v1 |
| resolve_codec | src/lib/common/structural/resolve/resolve_codec.spl | CPU reference codec (oracle) | frozen v1 |
| facade | src/lib/common/structural/resolve/__init__.spl | explicit exports | frozen v1 |
| gpu_smf linker | src/compiler/70.backend/linker/gpu_smf/ | SmfLinkProfile L0–L12 | not started |
| StyleLinker | (Wave 6/7) | WebResourceLinkProfile | not started |

Dependency Map: resolve → identity + wire (read-only); gpu_smf → resolve +
placement_contracts (resident tier) + existing `70.backend/linker` SMF
reader/writer as parity oracle. Contract doc:
`doc/05_design/platform/structural_compute/link_manager_contract_v1.md`.

## Phase

implement-smf-profile-skeleton-done

## Log

- 2026-07-31 dev: digested origin updates (ID-TAG freeze `9abe893428f`,
  layout framework `fca0b2a5981`, gpu_mmu residency freeze `75e6b1e8435b`,
  DrawIR v3 binding `1c945f320e0`) via three parallel readers before design.
- 2026-07-31 arch/design: froze resolve contract v1 — types, codec, facade,
  golden vectors (hand-derived), contract spec; ambiguities table raised in
  contract doc §7 (ResolveKey width, attributes/order width, group_key
  parameter type, spec dir, MutationIR ownership). Landed `1a6b00f5da1`.
- 2026-07-31 implement: three parallel lanes with guides
  (.spipe/link_manager/LANE_GUIDE.md). CORE: resolve_core.spl (sha256-based
  intern, stable merge sort, group/reduce) spec 7/7 + red sentinel; raised
  §7 row 6 (reason on Resolved with duplicates). FRONTIER:
  resolve_frontier.spl (BFS reachability, OR-fixpoint with explicit cap
  failure) spec 9/9 + red sentinel. SMFMAP: smf_linker_map.md — existing
  linker covers only part of L0–L12 (L2/L3/L10/L12 absent,
  symbol_analysis/reloc_engine are dead code, live L7–L9 via external cc);
  parity harness verified deterministic; found `compile --format=smf` nil
  receiver crash (bug doc compile_format_smf_nil_receiver_crash_2026-07-31).
- 2026-07-31 note: facade __init__.spl deliberately still exports only the
  frozen contract surface; core/frontier are imported by submodule path
  until gpu_smf consumes them.
- 2026-07-31 implement: SMFPROFILE lane landed the gpu_smf skeleton —
  smf_link_profile.spl (smf_collect_records L2/L3 + smf_resolve L3/L4 over
  resolve_core; SmfSymbolInput caller-supplied because SmfReaderImpl.symbols
  is only populatable via an SFFI handle on a real .smf file) spec 5/5 + red
  sentinel. attributes=0 deferred to the L1-decode wave per contract §6.
- Next: L1 integration wave — thin adapter SmfReaderImpl.symbols ->
  [SmfSymbolInput] (derive defined from size/section_index) against a real
  on-disk .smf fixture; then attributes-bit freeze, reachability wiring
  (resolve_frontier over section edges), and the byte-parity harness per
  smf_linker_map.md §5. Blocked oracle: compile --format=smf crash (bug doc
  compile_format_smf_nil_receiver_crash_2026-07-31).
