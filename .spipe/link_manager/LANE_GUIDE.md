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
