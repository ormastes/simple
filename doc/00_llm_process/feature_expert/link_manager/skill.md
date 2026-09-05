# Feature Expert: link_manager (LINK lane)

Accurate to landed work through `85c1338abfd` (wave 6). Later waves must
update this file per the Update Rule below.

## What this is

The LINK lane of the structural-compute program: **GraphResolveCore** — a
shared, deterministic symbol-resolution core (records, hash/intern, stable
sort/group, group reduction, reachability frontiers, constraint propagation,
cycle detection) — plus **profiles** that share the primitives but never the
semantics:

- `SmfLinkProfile` — the SMF linker pipeline (stages L0 discover … L12
  manifest commit) in `src/compiler/70.backend/linker/gpu_smf/`.
- `WebResourceLinkProfile` / StyleLinker — stylesheet imports,
  custom-property graph, fonts, keyframes (skeleton only as of wave 6;
  cycle-detection wiring pending).
- `ClangOffloadLinkProfile` — future, after clang_bridge C1 lands.

Spatial layout is NOT a profile; native ELF/Mach-O/PE stays on native
linkers. Contract freeze landed `1a6b00f5da1`; Phase-1 CPU lanes followed in
waves through `85c1338abfd`.

## Frozen surfaces (do not change without a schema bump)

Contract doc: `doc/05_design/platform/structural_compute/link_manager_contract_v1.md`.

- **Wire layout, RESOLVE group schema v1 (contract §3):** `ResolveKey`
  (20 B: Hash128 name_hash + u32 space), `DefinitionRecord`/`ReferenceRecord`
  (44 B, magics `SDFN`/`SRFR`), `ResolutionRecord` (20 B, magic `SRSL`).
  Enums on the wire as u8, unknown = hard reject: `ResolveStatus` (0
  Unresolved by design, so zeroed arena memory never reads as success),
  `ResolveReason`, `LinkMutationKind`, `ResolveMode` (CpuReference is the
  byte-oracle for hybrid/resident).
- **Interface surface (contract §4):** `ResolveProfile` six-step trait
  (collect / group_key / resolve_group / derive_constraints / plan_placement
  / emit); arena handles are `object_slot`/`generation` pairs, never wire
  records or raw addresses; stage ids `SMF_LINK_STAGE_L0_DISCOVER` …
  `L12_MANIFEST_COMMIT` (values 0–12) keying `StageReceipt.stage`; frozen
  `link.*` tag names (symbol.{binding,visibility,resolution},
  section.{kind,alignment}, relocation.kind, reachable, icf.candidate,
  hot_order, output_range).
- **SMF_LINK_ATTR schema v1** (`smf_link_attributes.spl`,
  `SMF_LINK_ATTR_SCHEMA_VERSION = 1`, wave 5 Lane ATTR): u64 — bit 0
  defined, bits 1–2 binding (3 = reject), 3–4 sym_type, 5–6 layout_phase,
  bit 7 event-loop anchor, bit 8 layout_pinned, bits 9–63 reserved
  (hard-reject if set). Total decoder with explicit `ok` carrier.
- **Reused, not redefined:** identity (`EntityRef`/`SnapshotId`/`Hash128`),
  `structural/wire.spl` byte conventions, `StageReceipt`/placement from
  `compute/placement_contracts` — no parallel identity/wire/receipt types.
- Versioning: any change bumps `RESOLVE_SCHEMA_VERSION` and adds
  `resolve_golden_v2`; **golden vectors are never edited in place**; the CPU
  reference codec is never deleted (contract §5).

## Oracle decisions (user, 2026-07-31)

1. **SMF byte parity has no oracle.** The in-tree SMF reader/writer are
   unimplemented scaffolding: `rt_smf_reader_open` has NO implementation
   anywhere and `SmfWriter.write()` unconditionally returns `Ok([])` (bug doc
   `smf_reader_writer_externs_unimplemented_2026-07-31`). Phase-1 acceptance
   (AC-3) was re-scoped to (a) deterministic native-build/cc parity gated by
   `scripts/check/check-link-native-build-parity.shs` (green sha256 proven,
   red-proofed on a bogus entry) and (b) resolve-layer byte parity vs the
   frozen CPU reference codec goldens. SMF-level byte parity stays deferred
   behind the externs bug.
2. **No in-tree CSS custom-property resolver.** The wave-6 STYLE scout
   (`.spipe/link_manager/style_resolver_map.md`, in commit `85c1338abfd`)
   proved nothing in-tree builds a `--x` / `var(--x)` name graph — the
   browser's C++ side dereferences `var()`; in-tree code only emits opaque
   CSS text, plus textual `@import`/`@font-face` URL extraction. So "parity
   vs current resolver" (AC-4) has no oracle either; acceptance re-pinned to
   the scouted real shapes in the spec. `detect_cycles` landed in
   `resolve_frontier.spl` (Kahn peel + BFS membership refinement — raw Kahn
   over-approximates); wiring into `style_resolve` is pending.

## Verification discipline

- Run each spec with the bootstrap seed runner, one spec at a time:
  `src/compiler_rust/target/bootstrap/simple test <spec>` — capture output
  to a file and read the final `Results:` line.
- **Red sentinel before green claim:** prove non-vacuity with a deliberate
  failing assertion, then remove it, before reporting a spec green. Wave-6
  integration state: 79/79 across the 7 lane specs re-run in one tree.
- Golden vectors are hand-derived from contract §3 (never captured from the
  encoder) and never edited in place.
- `git hash-object -w` every new/edited file immediately and record blob
  hashes — the shared WC deleted fresh files twice on 2026-07-31. A WC on a
  divergent head may lack wave-6 files (e.g. `smf_link_receipts.spl`,
  `style_link_profile.spl`, `style_resolver_map.md`); recover with
  `git show 85c1338abfd:<path>`.
- Lane rules: struct + free functions for wire-adjacent data (no
  inheritance), no `Dict.len()` / `.get()` on struct-valued dicts, no
  indexed-assign mutation (COLL019), no TODO comments, placeholders fail
  explicitly (`assert(false)` / `fail(...)`).

## File map (as of 85c1338abfd)

| Path | Role |
|---|---|
| `src/lib/common/structural/resolve/resolve_types.spl` | frozen records/enums/trait/stage ids/tags |
| `src/lib/common/structural/resolve/resolve_codec.spl` | CPU reference codec (the oracle) |
| `src/lib/common/structural/resolve/resolve_core.spl` | intern (sha256-based Hash128), stable merge sort, group/reduce |
| `src/lib/common/structural/resolve/resolve_frontier.spl` | BFS reachability, OR-fixpoint with explicit cap failure, detect_cycles |
| `src/lib/common/structural/resolve/style_link_profile.spl` | StyleLinker skeleton (STYLE_SPACE_* 16–19, StyleLinkResult) |
| `src/lib/common/structural/resolve/__init__.spl` | facade — exports only the frozen contract surface; core/frontier imported by submodule path |
| `src/compiler/70.backend/linker/gpu_smf/smf_link_profile.spl` | smf_collect_records (L2/L3) + smf_resolve (L3/L4) over resolve_core |
| `src/compiler/70.backend/linker/gpu_smf/smf_link_attributes.spl` | frozen attributes u64 codec, schema v1 |
| `src/compiler/70.backend/linker/gpu_smf/smf_reader_adapter.spl` | SmfWriterSymbol -> SmfSymbolInput (defined = size>0 OR section_index>=0) |
| `src/compiler/70.backend/linker/gpu_smf/smf_reachability.spl` | resolve_frontier over section edges |
| `src/compiler/70.backend/linker/gpu_smf/smf_link_receipts.spl` | StageReceipt wrappers, stage "smf_link.L<n>", sha256 roots, no timestamps |
| `test/01_unit/common/structural/resolve_contract_spec.spl` | contract spec: exact bytes, round trips, total-decoder rejects |
| `test/01_unit/common/structural/{resolve_core,resolve_frontier,style_link_profile}_spec.spl` | lane specs |
| `test/01_unit/compiler/linker/gpu_smf/*_spec.spl` | attributes / profile / reachability / adapter / receipts specs |
| `test/fixtures/structural/resolve_golden_v1.{spl,sdn}` | hand-derived golden vectors |
| `scripts/check/check-link-native-build-parity.shs` | Phase-1 parity gate (native-build/cc route) |

Scout/state docs: `.spipe/link_manager/{state.md,LANE_GUIDE.md,smf_linker_map.md,style_resolver_map.md,hybrid_batch_notes.md}`.
`smf_linker_map.md` maps L0–L12 onto today's linker: L2/L3/L10/L12 have no
current equivalent, `symbol_analysis.spl`/`reloc_engine.spl` are dead code,
live L7–L9 run inside the external `mold`/`lld`/`ld`/`cc`.
`hybrid_batch_notes.md` records batch shapes vs frozen widths and 10 open
questions (incl. missing L7/L8 CPU oracles, nondeterministic elapsed_us).

## Known bugs (open)

- `bin/simple compile --format=smf` crashes (`field access on nil receiver`,
  exit 132) — bug doc `compile_format_smf_nil_receiver_crash_2026-07-31`;
  the parity harness uses `native-build` on
  `examples/01_getting_started/hello_native.spl` instead.
- SMF reader/writer externs are scaffolding (see Oracle decision 1) — bug
  doc `smf_reader_writer_externs_unimplemented_2026-07-31`. Implementing
  `rt_smf_reader_open`/`rt_smf_write` is runtime-owned and needs bootstrap;
  not essential for Phase 1.

## Feature Links

- Plan: `doc/03_plan/platform/structural_compute/link_manager_plan.md`
- Design/contract: `doc/05_design/platform/structural_compute/link_manager_contract_v1.md`
  (§7 ambiguities table = decisions raised back to the architecture owner)
- State/log: `.spipe/link_manager/state.md`
- Layer expert: [backend](../../layer_expert/backend/skill.md)
  (gpu_smf lives under `src/compiler/70.backend/linker/`)

## Update Rule

When a wave lands, an oracle decision changes, a frozen surface gains a
schema bump, or a bug doc opens/closes, update the sections above and the
`.spipe/link_manager/state.md` log in the same change. Template:
`.spipe/spipe/doc/00_llm_process/template/feature_skill.md`.
