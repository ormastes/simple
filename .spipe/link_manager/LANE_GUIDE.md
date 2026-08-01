# link_manager Phase 1 lane guide (CPU core wave)

Base: frozen resolve contract v1 (`1a6b00f5da1`), contract doc
`doc/05_design/platform/structural_compute/link_manager_contract_v1.md`.
All lanes: struct + free functions (no inheritance/classes for wire-adjacent
data), reuse `structural/wire.spl` + `structural/identity`, no `Dict.len()`/
`.get()` on struct-valued dicts, no indexed-assign mutation (COLL019), no
TODO comments (implement or omit), placeholder helpers fail explicitly.
Verify each spec with the bootstrap seed
(`src/compiler_rust/target/bootstrap/simple test <spec>` — single spec at a
time, capture to a file, read the final `Results:` line) and prove
non-vacuity with a deliberate-red sentinel before reporting green.
Immediately `git hash-object -w` every new/edited file and report blob
hashes — the shared WC has deleted fresh files twice on 2026-07-31.

## Lane CORE — GraphResolveCore CPU primitives

`src/lib/common/structural/resolve/resolve_core.spl` +
`test/01_unit/common/structural/resolve_core_spec.spl`.
Deliver: name interning to `Hash128` (reuse an existing 128-bit or paired
64-bit hash from `src/lib/common/{hash,crypto}` — never a new hash), stable
sort of Definition/ReferenceRecords by (key, order), grouping into
`ResolveGroupView` slices, deterministic group reduction (lowest-`order`
definition wins; later duplicates produce `DuplicateDefinition` diagnostics
in stable order). Pure arrays, O(n log n) via an existing stdlib sort.

## Lane FRONTIER — reachability + constraint propagation

`src/lib/common/structural/resolve/resolve_frontier.spl` +
`test/01_unit/common/structural/resolve_frontier_spec.spl`.
Deliver: edge-array frontier expansion (worklist BFS over
`EntityRef -> EntityRef` edges, u32 slot/index pairs), reachability marking
for dead-strip (`link.reachable`), and a bounded constraint-propagation
fixpoint (iterate until no change, hard cap = edge count, cap hit returns an
explicit failure — never a silent partial result).

## Lane SMFMAP — existing SMF linker map (read-only scout)

Output: `.spipe/link_manager/smf_linker_map.md` only — NO code changes.
Map `src/compiler/70.backend/linker/` (entry points, symbol/section/reloc
data flow, output write path, archive handling) onto pipeline stages L0–L12
from the contract doc §4; identify for each stage the existing function(s)
that own it today; specify the byte-parity harness (how to run the current
SMF link twice on a fixture input and hash outputs) that Phase 1 acceptance
("byte-identical output") will use.

# Phase 1 wave 5 (post oracle re-scope, base commit 674cd143454a)

Oracle decision (user, 2026-07-31): SMF byte parity is deferred behind bug
doc `smf_reader_writer_externs_unimplemented_2026-07-31`; acceptance gates on
`scripts/check/check-link-native-build-parity.shs` + the frozen CPU codec
goldens. Same shared rules as above; branch worktrees from `674cd143454a`.

## Lane ATTR — SmfLinkProfile attributes-bit freeze

Files: `src/compiler/70.backend/linker/gpu_smf/smf_link_attributes.spl` (new),
extend `smf_link_profile.spl` / `smf_reader_adapter.spl` only where needed,
spec `test/01_unit/compiler/linker/gpu_smf/smf_link_attributes_spec.spl`,
and amend contract doc §6 (attributes item moves to "frozen — see
smf_link_attributes.spl", schema `SMF_LINK_ATTR_SCHEMA_VERSION = 1`).
Freeze `SMF_LINK_ATTR_*` bit constants over what `SmfWriterSymbol`
(smf_writer.spl:137) actually carries: defined flag, binding, sym_type,
layout_phase (2 bits), is_event_loop_anchor, layout_pinned. Low bits first,
document each bit range in the docstring; unused high bits must encode as 0
and the decoder-side helper must hard-reject set unknown bits (total, like
the wire codec). Deliver encode (`SmfSymbolInput`-side fields -> u64
attributes) + field extractors, wire into `smf_collect_records` so
Definition/ReferenceRecords carry real attributes, extend `SmfSymbolInput` +
the writer-symbol adapter with the new fields (u32/bool in-memory scalars —
never u8 struct fields). Spec: exact expected u64 values for hand-computed
cases, round-trip extractors, reject-unknown-bit, adapter mapping, red
sentinel proof.

## Lane REACH — reachability wiring over section edges

Files: `src/compiler/70.backend/linker/gpu_smf/smf_reachability.spl` (new) +
spec `test/01_unit/compiler/linker/gpu_smf/smf_reachability_spec.spl`.
Wire `resolve_frontier` (reuse `ResolveEdge`/`ReachableResult` — import from
`src/lib/common/structural/resolve/resolve_frontier.spl`, do NOT redefine)
over caller-supplied section edges: `smf_reachable_sections(section_count,
edges, roots) -> ReachableResult` (thin, bounds-rejecting wrapper) and
`smf_unreachable_symbol_indices(inputs: [SmfSymbolInput], marks) -> [u32]`
(defined symbols whose section is unmarked, stable input order; undefined
symbols and out-of-range section_index are never listed — reference records
don't get dead-stripped, they get MissingDefinition later). No wire format,
no new batch layouts (contract §6 keeps those deferred). Spec: linear chain,
diamond, unreachable island, empty roots, bounds reject, stable order, red
sentinel proof.

# Phase wave 6 (4 parallel lanes, base ae87d52fbdf1)

Shared rules unchanged (top of file). File ownership is DISJOINT — never edit
another lane's files; integration re-run happens at landing.

## Lane PROFILE — SmfSymbolInput section_index + StageReceipts

Owns: `src/compiler/70.backend/linker/gpu_smf/*` + its specs. Fold
`section_index: i64` (negative = no section, from `SmfWriterSymbol`) into
`SmfSymbolInput`; adapter populates it; retire the parallel
`section_indices` argument of `smf_unreachable_symbol_indices` (read the
struct field instead) and update its spec accordingly. Then wire
`StageReceipt` (from `compute/placement_contracts` — read its real shape,
never redefine) into the profile: each of collect/resolve/reachability
produces a receipt keyed by the matching `SMF_LINK_STAGE_L*` const, in a new
`smf_link_receipts.spl` helper + calls from the profile. Deterministic
receipt content only (counts/hashes — no timestamps). All four gpu_smf
specs green + red sentinel on the receipt spec.

## Lane CYCLE — deterministic cycle detection in resolve_frontier

Owns: `src/lib/common/structural/resolve/resolve_frontier.spl` +
`test/01_unit/common/structural/resolve_frontier_spec.spl` (append; never
weaken existing examples). Add `CycleResult { ok: bool, has_cycle: bool,
cycle_members: [u32] }` and `detect_cycles(node_count, edges: [ResolveEdge])
-> CycleResult`: deterministic (iterative Kahn peel or DFS with explicit
stack — no recursion), cycle_members = all nodes on at least one cycle in
ascending index order, same bounds-reject discipline as reachable_mark.
Feeds ResolveReason.CycleDetected (StyleLinker custom-property graphs, plan
Wave 6/7). Spec: acyclic chain/diamond, self-loop, 2-cycle, two disjoint
cycles, cycle+tail (tail not a member), bounds reject, red sentinel.

## Lane STYLE — WebResourceLinkProfile scout + skeleton

Owns: NEW files only — `src/lib/common/structural/resolve/style_link_profile.spl`
+ `test/01_unit/common/structural/style_link_profile_spec.spl` + scout notes
`.spipe/link_manager/style_resolver_map.md`. First SCOUT the current web
resource/custom-property resolution (grep for custom property / var() /
stylesheet import resolution under `src/lib/common/` ui/style and web dirs;
record file:line owners + data shapes in the map — read-only). Then a
minimal profile skeleton over resolve_core in the frozen-contract style:
`STYLE_SPACE_*` u32 space consts (custom_property, import, font_face,
keyframes — distinct from SMF_SPACE_*), `StyleSymbolInput`,
`style_collect_records` -> Definition/ReferenceRecords,
`style_resolve(defs, refs) -> [ResolutionRecord]` via resolve_core, and
`StyleLinkResult` (plan line 40: html_css_parser consumes it) holding
resolutions + unresolved names. Cycle detection NOT wired this wave (CYCLE
lane lands the primitive concurrently — note it as next). Parity vs the
current resolver is examples-level only this wave: derive at least 2 spec
cases from real shapes found in the scout. Spec green + red sentinel.

## Lane HYBRID — hybrid batch shapes design notes (docs only)

Owns: `.spipe/link_manager/hybrid_batch_notes.md` only — NO code. Map each
CPU primitive (intern/sort/group/reduce in resolve_core; reachable_mark /
propagate_constraints in resolve_frontier) onto plan Wave-7 GPU batch stages
(hash/sort/resolve/reachability/scan/relocation): for each, input/output
array shapes (element widths from the frozen wire layouts), what stays CPU
(decode/control), which placement_contracts calls (leases, StageReceipt)
bracket each batch, and the parity gate (batch output must byte-match the
CPU codec per contract §5.3). End with open questions for the freeze —
freeze itself stays deferred per contract §6.

# Phase wave 7 (4 parallel lanes, base 85c1338abfdd)

Shared rules unchanged. Ownership DISJOINT; integration re-run at landing.

## Lane STYLE2 — cycle detection wired into the style profile

Owns: `src/lib/common/structural/resolve/style_link_profile.spl` +
`test/01_unit/common/structural/style_link_profile_spec.spl` (append; never
weaken existing 7). Build the custom-property dependency graph inside
`style_link`: nodes = distinct ResolveKeys (custom-property space only),
edges = definition-body references (extend `StyleSymbolInput` with
`referenced_names: [text]` — a custom property whose VALUE contains var(--x)
depends on --x), run `detect_cycles` from resolve_frontier (import; never
reimplement), and for every resolution whose key is a cycle member set
status Resolved -> Ambiguous? NO — per contract §3 semantics set status
unchanged but reason CycleDetected ONLY when the record's key is a cycle
member; also surface `cycle_property_names: [text]` (ascending, deduped) on
StyleLinkResult. Non-custom-property spaces never enter the graph. Spec:
2-cycle (--a<->--b), self-loop, cycle+tail (tail resolves clean, reason
Unspecified), acyclic var() chain (no cycle flags), cross-space immunity,
red sentinel.

## Lane BATCH — CPU-side columnar batch flattening (hybrid prep)

Owns: NEW `src/lib/common/structural/resolve/resolve_batch.spl` +
`test/01_unit/common/structural/resolve_batch_spec.spl`. Per
hybrid_batch_notes.md (read it), hybrid batches need columnar arrays. Deliver
pure CPU transforms with `ok` result structs: `batch_flatten_names([text])
-> { ok, blob: [u8]?, offsets: [u32] }`-style name-blob+offsets (u32
offsets, blob is concatenated bytes, offsets.len = names.len+1),
`batch_flatten_definitions/[references]([Record]) -> columnar struct` (one
array per field, widths matching the frozen wire layout §3), and exact
inverses. Parity gate: flatten -> rebuild -> encode via resolve_codec must
be byte-identical to encoding the originals (assert via wire_to_hex on at
least 3 mixed records including max-value fields). This is measurement
groundwork for the batch-layout freeze — do NOT touch the contract doc; no
new wire formats, in-memory only. Red sentinel.

## Lane RELOC — relocation formula CPU oracle (L8 groundwork)

Owns: NEW `src/compiler/70.backend/linker/gpu_smf/smf_reloc_formulas.spl` +
`test/01_unit/compiler/linker/gpu_smf/smf_reloc_formulas_spec.spl`. Read
`RelocationType` + `SmfRelocation` in `src/compiler/70.backend/linker/`
(smf_writer.spl:148 area; find every variant and where existing code
computes or documents each formula — cite in docstring). Deliver pure
formula functions (i64 in/out, no memory writes): for each RelocationType
variant the canonical formula (e.g. Abs64 = S+A, Pc32 = S+A-P truncated
with explicit range check) as `smf_reloc_compute(reloc_type, s, a, p) ->
{ ok, value }` — out-of-range PC32 (doesn't fit i32) rejects ok:false,
never silent truncation. Unknown variant rejects. Spec: hand-computed
fixtures per variant (positive, negative addend, PC-relative crossing zero,
range-reject at exactly i32 boundary ±1), totality reject, red sentinel.
This is the missing L8 CPU oracle flagged in hybrid_batch_notes.md — code
only, no contract-doc edits.

## Lane WIKI — LLM wiki entries (docs only, vcs.md rule)

Owns: `doc/00_llm_process/feature_expert/link_manager/skill.md` (new) and,
if a fitting layer dir exists or the template mandates one,
`doc/00_llm_process/layer_expert/<layer>/skill.md` touched minimally. Use
templates `.spipe/spipe/doc/00_llm_process/template/{feature,layer}_skill.md`
and mirror an existing feature_expert entry's structure (read 1-2 siblings
first). Content from: `.spipe/link_manager/state.md`, contract doc,
smf_linker_map.md, style_resolver_map.md, hybrid_batch_notes.md. Cover: what
the LINK lane is, frozen surfaces, oracle decisions (SMF externs bug, no CSS
resolver), verification discipline (seed runner + red sentinels), file map.
NO code. Keep it accurate to landed commits only (through 85c1338abfd).
