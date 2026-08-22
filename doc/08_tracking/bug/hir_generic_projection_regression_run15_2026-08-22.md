# Stage-1 HIR regression: generic-projection lanes take fatals 48 -> 3716 (run15)

- **Status:** REVERTED on main; underlying defect REFILED (below), not fixed.
- **Filed:** 2026-08-22
- **Reverted commits:** `d481f15e1ac` (generic-argument projection), `86787968989` (generic-callable signature projection + `Function` arm)
- **Kept:** `4a40c00c8e5`, `9f11967564b` (array-of-tuple / pointer / union), `22a0424891a` (payload-origin miss memo)

## Measurement

All counts on the `[hir-fatal]` basis, from full stage-1 builds.

| tree | fatals | poisoned modules |
|---|---|---|
| run14 `75a66d615bd` | 258 | 56 |
| post19 (array-of-tuple only, §27 row for `4a40c00c8e5`) | **48** | **9** |
| run15 `b99deb6ae58` | **3716** | **437** |

Non-fatal recovered `unresolved type` occurrences went the OTHER way, 234,210 ->
7,231, which is why the lanes looked like progress on a raw grep. Recorded so
the next reader is not misled: the two numbers move in opposite directions and
only the fatal count gates the build.

## What is new in run15, and what is not

Every one of the 3716 fatal names is a user-declared type. `Option`, `Result`
and `Dict` are **not** among them — they resolve; their ARGUMENTS do not.

| name | fatals | shape in the owner |
|---|---|---|
| HirContractBlock | 501 | `verification_contract: HirContractBlock?` — `50.mir/mir_instruction_graph.spl:208` |
| SymbolId | 444 | `owner_symbol: SymbolId?` — `module_callable_types.spl:88` |
| MirFunction | 171 | field/optional positions in the same graph module |
| ModuleSurfaceExportOrigin | 159 | optional/dict positions |
| HirType | 144 | `hir_types.{SymbolId, HirType}` import at graph:3 |
| Span | 141 | `span: Span?` — `mir_instruction_graph.spl:14` |
| LayoutPhase | 84 | `layout_phase: LayoutPhase?` — `mir_instruction_graph.spl:177` |

`mir_instruction_graph.spl` **imports** all four of Span, HirType,
HirContractBlock and LayoutPhase (lines 3-5) and declares none of them. The
victim, `50.mir/hwir/bit_vector_constant.spl`, has **no `use` line at all** and
reports exactly those four names.

## Mechanism (static, from the diffs and the tree)

`imported_surface_projected_named_args` now recurses into each generic
ARGUMENT and calls
`self.symbols.lookup_qualified_type_raw(imported_module_name, arg_name)`.
`imported_module_name` is the module the importer NAMED — here a package facade
reached by sibling auto-import / glob re-export — not the module that DECLARES
the argument type. The lookup misses; `imported_surface_type` then falls through
to `self.lower_type`, which resolves in the **importer's** scope and emits a
hard, non-recovered `unresolved type: X` against a module that never names X.

The profile line for the victim shows the miss rate directly:
`qtype=4725/3781 miss` — 80% of qualified type lookups miss.

`86787968989` compounds it: removing the `callable.type_params.len() > 0` bail
plus adding the `Function` arm feeds the whole generated visitor/codec
population through the same broken lookup.

**Widening projection did not create the resolution gap. It made an existing
one fatal at scale.** The gap is the same owner-scope/re-export-hop resolution
already filed as `hir_unresolved_type_owner_missing_import_2026-08-22.md`.

## Why revert rather than fix forward

The correct fix is owner-scope resolution that follows the re-export hop to the
DECLARING module — NOT restoring the drop, which is the original silent defect
(`d481f15e1ac` proved the drop silently erased `Dict<text,MirType>` to
`Dict<any,any>`). That is a resolver change whose only oracle is a ~5 h stage-1
build, so it could not be landed and validated in this window. 437 poisoned
modules must not sit on main overnight, so the lanes are reverted and the defect
stays open.

## Honest limits of this investigation

- **No unit fixture reproduces it.** `test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl` was written for this record and is GREEN on both sides. A four-module `export use` facade hop is not sufficient; the real trigger involves package-sibling auto-import and `use ...*` globs. Kept as a non-vacuous guard, labelled as not-a-reproducer in its own docstring.
- **Per-commit attribution is static, not measured.** Two targeted `native-build --entry-closure` probes were attempted; neither reached the HIR phase for the victim module (rc=1 in 178 s, 0 `[hir-fatal]`). The split above rests on the diffs plus the shape of the failing names (all `X?`/generic-argument positions), not on a differential build.
- **Pre-existing red, stepped over and recorded:** `imported_surface_callable_projection_spec.spl` is 2 of 3 RED at pristine `c05e7052843` AND byte-identical after the revert. Not caused by this change.

## Next lane

Fix `lookup_qualified_type_raw` (or its caller) to resolve a projected argument
in the module that DECLARES it, following the owner's import table and
re-export hops, then re-land `d481f15e1ac` and `86787968989` behind a measured
stage-1 census. Do not re-land either without that census.
