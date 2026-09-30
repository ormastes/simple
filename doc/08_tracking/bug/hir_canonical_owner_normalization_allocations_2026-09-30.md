# Repeated HIR canonical owner normalization allocates temporary strings

Status: source fix implemented; runtime qualification recorded in the report below.

The Linux Phase 3 producer with SHA-256
`9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`
was sampled in `SymbolTable.lookup_qualified_type_raw` calling
`_hir_symbol_owner_module`, `module_logical_name_from_path`, substring search
and per-byte runtime heap validation. The qualified lookup already had an
index; constructing its key still normalized every canonical module operand.

The old normalizer splits and rejoins dotted names and rebuilds sanitized text
one character at a time. A canonical input such as
`compiler.hir.hir_lowering.module_callable_types` needs none of that work.

`hir_owner_name.spl` now validates ASCII dotted identifiers and returns the
original text directly. It conservatively sends empty names/segments,
numeric-leading segments, `std` aliases, `.spl`/`.sdn` suffixes, paths,
punctuation and Unicode to the unchanged normalization algorithm. The existing
private symbol-table helper delegates to this pure module. No cache, symbol
table layout or transient ownership contract changes.

The native fixture compares 32 spellings against the old algorithm, then
measures heap registry growth for 256 canonical calls to each implementation.
The unit spec additionally checks qualified hits/misses, first binding and
module reset across canonical/path spellings. The canonical allocation budget
does not apply to alias folding or fallback normalization.

Two observed RSS values (4.37 and 6.08 GiB) do not establish a leak: the driver
retains completed HIR and per-module symbol snapshots. This patch targets
avoidable transient work; it does not promise a particular whole-build RSS or
wall-time improvement.

Evidence and limitations:
`doc/09_report/hir_owner_name_fast_path_2026-09-30.md`.
