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
- AC-3 (Phase 1, RE-SCOPED 2026-07-31 by user decision): the in-repo SMF
  writer/reader are unimplemented scaffolding (bug doc
  smf_reader_writer_externs_unimplemented_2026-07-31), so "byte-identical SMF
  output" has no oracle. Phase-1 acceptance is now: (a) deterministic
  native-build/cc parity per smf_linker_map.md §5 (gated by
  scripts/check/check-link-native-build-parity.shs), and (b) resolve-layer
  byte parity vs the frozen CPU reference codec (golden vectors). SMF-level
  byte parity is deferred behind the externs bug.
- AC-4 (later; NOTE 2026-07-31): StyleLinker/WebResourceLinkProfile —
  wave-6 scout proved NO symbol-level custom-property resolver exists
  in-tree (var()/--x are opaque generated text; only textual @import /
  @font-face URL extraction exists — see style_resolver_map.md), so "parity
  vs current resolver" has no oracle; acceptance pins real scouted shapes
  in the spec instead. Custom-property cycle detection: detect_cycles
  primitive landed, wiring pending.

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
| gpu_smf linker | src/compiler/70.backend/linker/gpu_smf/ | SmfLinkProfile L0–L12 | L1–L6 slice + attrs + receipts + reachability |
| StyleLinker | src/lib/common/structural/resolve/style_link_profile.spl | WebResourceLinkProfile | skeleton (cycle wiring pending) |

Dependency Map: resolve → identity + wire (read-only); gpu_smf → resolve +
placement_contracts (resident tier) + existing `70.backend/linker` SMF
reader/writer as parity oracle. Contract doc:
`doc/05_design/platform/structural_compute/link_manager_contract_v1.md`.

## Phase

implement-cycles-batch-reloc-wiki-done

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
- 2026-07-31 implement: L1ADAPT lane landed smf_reader_adapter.spl
  (SmfWriterSymbol -> SmfSymbolInput, defined = size>0 OR section_index>=0)
  spec 6/6 + red sentinel; sibling profile spec still 5/5. Route (a) on-disk
  fixture and (b) writer round-trip both PROVEN dead: no .smf fixture
  in-tree, rt_smf_reader_open has NO implementation anywhere, and
  SmfWriter.write() unconditionally returns Ok([]) — SMF I/O is scaffolding
  (bug doc smf_reader_writer_externs_unimplemented_2026-07-31).
- 2026-07-31 DECISION (user): re-scope the Phase-1 parity oracle to the
  native-build/cc route (AC-3 above). Implementing rt_smf_reader_open /
  rt_smf_write stays open as the externs bug doc — runtime-owned, needs
  bootstrap, not essential for Phase 1. runtime_need: real
  rt_smf_reader_open/rt_smf_write; facade_checked: yes (none exists — both
  are unimplemented externs); chosen_path: re-scope acceptance, keep bug
  filed; rejected_shortcuts: spec-local rt_* externs, fabricated .smf bytes.
- 2026-07-31 implement (wave 5, base 674cd143454a): parity gate script
  scripts/check/check-link-native-build-parity.shs (green sha256 b9f37a50…,
  red-proofed on bogus entry). ATTR lane froze the attributes u64 layout
  (smf_link_attributes.spl, SMF_LINK_ATTR_SCHEMA_VERSION=1: bit0 defined,
  1–2 binding [3=reject], 3–4 sym_type, 5–6 layout_phase, 7 anchor,
  8 pinned, 9–63 reserved-reject; total decoder) wired into
  smf_collect_records; SmfSymbolInput gained the attr fields; contract doc
  §6 amended; spec 19/19 + red sentinel. REACH lane wired resolve_frontier
  over section edges (smf_reachability.spl: smf_reachable_sections +
  smf_unreachable_symbol_indices with parallel section_indices arg until
  SmfSymbolInput carries section_index); spec 11/11 + red sentinel.
  Cross-lane integration re-run in one tree: 11/19/5/6 all green.
- 2026-07-31 implement (wave 6, base ae87d52fbdf1, 4 parallel lanes):
  PROFILE — SmfSymbolInput gained section_index (parallel-array arg
  retired), new smf_link_receipts.spl reusing placement_contracts
  StageReceipt (stage "smf_link.L<n>", sha256 input/output roots, no
  timestamps; with-receipt wrappers live in receipts module to avoid a
  circular import), specs 15/15+10/10+7/7. CYCLE — detect_cycles in
  resolve_frontier (Kahn peel + BFS membership refinement — raw Kahn
  over-approximates: downstream tails never peel), spec 16/16. STYLE —
  style_link_profile.spl skeleton (STYLE_SPACE_* 16–19, StyleLinkResult)
  + style_resolver_map.md scout (NO current resolver exists — AC-4
  amended), spec 7/7. HYBRID — hybrid_batch_notes.md (batch shapes vs
  frozen widths, 10 open questions incl. missing L7/L8 CPU oracles,
  nondeterministic elapsed_us). All lanes red-sentinel proven;
  integration re-run of all 7 specs in one tree: 79/79 green.
- 2026-08-01 implement (wave 7, base 85c1338abfdd, 4 parallel lanes):
  STYLE2 — detect_cycles wired into style_link (edges from value-body
  var() references; reason=CycleDetected on cycle members, status
  untouched; cycle_property_names on StyleLinkResult, explicit char-code
  compare instead of raw text `<`), spec 12/12. BATCH — resolve_batch.spl
  columnar flatten/rebuild (name blob+u32 offsets, per-field arrays
  mirroring frozen §3; total rebuilds reject ragged/broken-offset/bad-
  UTF-8; parity gate: flatten->rebuild->encode hex-identical to encoding
  originals incl. max-positive fields), spec 13/13. RELOC — L8 CPU oracle
  smf_reloc_formulas.spl (all 5 RelocationType variants: Abs64 S+A,
  Rel32/PltRel32/GotRel32 S+A-P signed-32-checked, Abs32 unsigned-32;
  rejects where dead reloc_engine masked; wire-code entry rejects
  unknown), spec 31/31. WIKI — feature_expert/link_manager/skill.md +
  additive backend layer link (vcs.md LLM-wiki rule). All red-sentinel
  proven; integrated re-run 72/72 green. Shared-WC clobber recurred
  mid-wave (LANE_GUIDE wave-7 block reverted by parallel session) —
  landed from object-store blobs per protocol, no loss.
- Next: hybrid batch-layout freeze proper (batch shapes now measured by
  resolve_batch.spl — answer the 10 open questions in
  hybrid_batch_notes.md with the architecture owner); apply-side reloc
  (formula oracle exists, no applier); style-profile receipts once stage
  ids for non-SMF profiles are decided.
