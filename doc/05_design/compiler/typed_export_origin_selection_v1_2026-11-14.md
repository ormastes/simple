# Typed export-origin selection V1 — contract for review

Status: source implementation in progress; authored specs UNRUN. Not admitted or landed.
Base: a6000e548fbd9276c7d1e840436c1eb95751585d.

## Publication phase

Move authoritative selection after all configured import/export target arrays
are prepared and aligned inside module_surfaces_freeze, before freeze flags and
final semantic digests. Remove the three early name-only prepasses (registry,
retained driver, streaming driver). finish/finish_into remain the owners. No
pre-freeze name-index guess is published as selected evidence. Existing generated
hints remain inputs with their own provenance, not grants or synthetic import edges.

## Types and API

- ModuleSurfaceExportCategoryV1: Function, Struct, Class, Enum, Trait,
  TypeAlias, Constant, Bitfield. Text adapters reject unknown categories.
- ModuleSurfaceExportSelectionStateV1: Missing, Pending, Selected, Ambiguous,
  Unavailable. Only Selected has a complete typed terminal and retained hops.
- ModuleSurfaceExportHopKindV1: Direct, NamedImport, GlobImport, QualifiedExport. Generated hints and sibling inference remain unqualified;
  they cannot manufacture a Selected edge. Direct is an explicit terminal marker, never an empty
  edge list interpreted as success.
- ModuleSurfaceSelectedExportIndexV1: registry owner of aligned flat binding
  arrays and append-only flat hop arrays, registry generation, stable route
  generation, canonical digest and frozen flag. Binding key is physical surface + Declaration/Export role + category + local
  spelling before any candidate coalescing; index generation is checked on reads.
- ModuleSurfaceExportSelectionV1: immutable checked lookup result containing
  state/reason, source surface/category/local spelling, registry generation,
  winning tier, expected typed terminal (physical owner/category/source spelling/
  declaration projection key), and edge window.
- ModuleSurfaceExportHopV1: source binding + export row/item; kind; optional exact
  import row/item; selected target surface/category/BINDING spelling; target
  generation; expected typed terminal. Negative indices are allowed only for
  explicitly inapplicable source positions, never selected target identity.

`module_surface_selected_export_lookup_v1(registry, surface_index, category,
local_name) -> ModuleSurfaceExportSelectionV1` checks registry/index alignment and
generation. `module_surface_selected_export_hop_v1(registry, selection, offset)
-> Result<ModuleSurfaceExportHopV1,text>` validates the entire window and roles.
The old name-only lookup remains a compatibility adapter only when all populated
category results identify one compatible origin; otherwise it is unavailable.
No adapter selects an arbitrary category or reconstructs syntax after selection.
A separate `module_surface_selected_declaration_lookup_v1` preserves direct
declarations without pretending that they are explicit facade exports.

The ModuleSurface source-evidence reference/digest is reserved for the existing
producer DTO once that owner supplies its immutable checkpoint. Do not duplicate
that contract. Semantic selection is not a requester access grant.

## Resolution invariants

Direct declarations precede named imports, then matching glob imports, qualified
exports, retained generated hints and package sibling selection (the existing
precedence must be reviewed at each branch). Every competing route in the winning
tier participates: different typed terminals are ambiguous; all routes reaching
one typed terminal remain retained. A delayed/unavailable matching named route
blocks lower tiers and cannot be hidden by a presently resolved same-tier route.

Chains refer to the intermediate target binding, not its collapsed terminal.
Consumers may OR legally traversable retained alternatives for one export, but
separately illegal explicit imports still produce their own diagnostic. Explicit
private cannot be promoted. Missing terminal/category/source authority, invalid
row roles, misaligned windows, stale generation and unresolved cycles yield
Unavailable or an explicit resolver error, never an empty successful route.

The bounded graph algorithm must distinguish pending from absent, detect cycles
and converge before publication; repeated queries perform indexed reads, not
whole-tree selection or syntax replay. Snapshot arrays live in the registry owner,
not a transient per-file arena. Canonical digest includes typed bindings, chosen
tiers, ordered selected edge provenance and stable physical source identities;
process-local allocation generation is validated separately, not hashed as a
cross-build identity.

## Required authored scenarios (runtime remains unqualified)

Category/name collision; legal and illegal same-terminal alternatives; distinct
terminals in one tier; pending named route masking a glob; chained aliases;
actual frozen-target mismatch; direct versus missing provenance; explicit private;
cycle; generation/window corruption; named alias whose old export target was -1;
retained/streaming/full registry path parity; digest sensitivity and stable reads.

## Current conservative boundaries

The source implementation salts every surface selection digest with a stable
whole-registry selection digest to invalidate changed intermediate routes even
when the terminal stays fixed. This is conservative cache invalidation, not a
measured incremental-performance claim. Process-local generation is excluded.

Existing plain same-folder export inference still needs actual admitted directory
lookup evidence before it can produce a Sibling route. The existing physical-alias
fixture is retained as a compatibility requirement; it is not rewritten to hide
this missing integration. Generated textual hints alone never grant access.

No native execution, full compiler import check, MCP/LSP smoke, or performance
qualification has been run for this source slice.

Root decision: an admitted typed folder declaration inventory must cover every
candidate file for implicit sibling selection. Closure membership alone is not
that inventory. Reuse the existing HIR sibling namespace owner once its coverage
and declaration facts are authoritative; do not infer completeness from this
selected registry. This lane intentionally does not scan additional files.

Bitfield source-authority retention remains incomplete. A missing bitfield
projection is Unavailable rather than proof of absence. This conservatively
keeps affected name-only compatibility results and whole-surface cache identity
unavailable until the real producer retains those declarations/absence facts.
Typed available categories remain queryable; no complete-registry claim is made.
