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
