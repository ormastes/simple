# compiler_cli_build 'unresolved type: MirType' — chase nondeterminism (2026-10-13)

Lane: release_phase3 campaign, worktree wt-20261013-mirtype (branch
fix/mirtype-unresolved-20261013). Cycle-34 evidence:
.simple/storage/build/bootstrap/stage2-compiler-tests/.../logs/compiler_cli_build.log
('unresolved type: MirType' at src/compiler/60.mir_opt/mir_opt_integration.spl
+ 1913 further phase-3 errors). Status: REPRODUCED STANDALONE; ROOT CAUSE
LOCALIZED TO A LANE; NO FIX LANDED THIS CYCLE (see bottom).

## Dedup exonerated (checked first, per campaign suspicion)

A candidate built from tip 21ce36ed18f (which includes both HIR dedup commits
6bbd8c4a212 + 21ce36ed18f) reproduced the failure in the standalone
compiler_cli invocation (entry src/app/cli/_CliMain/main_and_help.spl,
SIMPLE_SCV_INVENTORY_COLD_INIT=1, threads=4): 1384 'unresolved type' errors,
5 of them MirType -- with ZERO hir-dedup events. The dedup commits are not
the cause and need no adjustment. (The dedup commits' own standalone
verification also showed 0 events; the duplicate-admission lane they guard
is verifier-only.)

## What the failing modules have in common

transient_owner.spl, hardware_codegen_types.spl, verification_codegen_types.spl,
c_codegen_adapter.spl, cuda_backend_port.spl contain ZERO literal 'MirType'.
The origin trace (SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1, types.spl:1501) shows
name=MirType with span_file EMPTY (0:0) -- a synthesized type reference from
IMPORTED CALLABLE SIGNATURE dependency materialization: e.g. transient_owner
imports compiler.mir.mir_lowering_types.{MirLowering}; the class's method
signatures mention MirType; materializing those dependencies in the importer
must bind MirType into the importer's scope via the re-export chase
(module_import_registration.spl:954-989 -> find_reexport_source /
find_reexport_source_walk, module_reexport_materialization.spl).

## Mechanism evidence (SIMPLE_BOOTSTRAP_DIAG=1 chase receipts)

- The chase walk reaches compiler.mir.mir_types for wanted=MirType with
  declares=true consistently (10/10 hop lines in the diag run) -- whenever
  the walk GETS THERE it succeeds.
- mir_data (facade hop target, composites=2) declares=false for MirType --
  correct: MirType is a bare per-item re-export (`export use
  compiler.mir.mir_types.{... MirType ...}` records route target -1/name ""),
  so resolution falls to the walk's package-sibling inference arm
  (module_reexport_materialization.spl ~290: unique sibling of package
  compiler.mir that declares the name).
- The sibling inference arm has NO diagnostic print; whether it ran and
  found zero/ambiguous siblings for the failing chases is UNOBSERVED.
- The failure is NONDETERMINISTIC across runs: the diag-instrumented run
  showed MirType chases found=true throughout and (by its log) no failure,
  while the plain and origin-trace runs failed with 5 MirType errors.
  Nondeterminism + order-dependence + a no-print inference arm = the chase
  state (visited-set/memo or sibling index content) differs per scheduling.

## Ruled out

- HIR dedup commits (zero dedup events in a failing run).
- Surface capacity/index: module_surface_name_position is a linear scan;
  module_surface_declares_item answers true consistently for mir_types.
- Registry replacement staleness: module surfaces freeze once per build
  (module_surfaces_freeze errors if already frozen); a generation guard on
  build_package_sibling_index was implemented and REVERTED as unproven-
  inert for this path (lowering.module_surfaces is assigned once by
  hirlowering_for_module).

## Next probe (one run, deterministic failing config: cold-init, threads=4,
## no diag perturbation)

Add an eprint to the sibling-inference arm of find_reexport_source_walk
(counting candidate siblings and their declares_item results for the wanted
name) plus a found=false summary keyed by wanted name, rerun the plain
config, and read why the MirType chases that fail never reach mir_types:
either the visited-set/memo reexport_root_memo_* records a false negative
for an earlier partial walk (memoization of a retryable miss --
find_reexport_source only memoizes negatives when state.complete and
state.valid; a partial-registry walk can poison the memo), or the sibling
list for package compiler.mir is observed empty at that moment.

## Probe results (SIMPLE_HIR_SIBPROBE, deterministic failing config) — 2026-10-13 second pass

Instrumented the sibling-inference arm (env-gated eprints in
module_reexport_materialization.spl). Findings:

1. The arm RAN for other names but NEVER for wanted=MirType -- MirType's hard
   errors come from a dependency-projection path that does not reach the arm.
2. DECISIVE: for wanted=OptimizationLevel/ManifestError/etc., the probe shows
   ONE surface with CROSS-WIRED IDENTITY:
     facade(preferred_registry_name)=compiler.mir_opt.optimization_passes
     module_name=lib.compiler.mir_opt.optimization_passes
     canonical_name=lib.compiler.mir_opt.optimization_passes
     package=lib.compiler.mir_opt  siblings=2 (the real src/lib/compiler/
     mir_opt tree) instead of compiler.mir_opt's ~40.
   The chase therefore searches the wrong package bucket, finds no
   declarant, and memoizes a negative -> hard 'unresolved type' in innocent
   importers. THE ROOT CAUSE LOCUS IS THE SURFACE IDENTITY CROSS-WIRE, not
   the chase and not the sibling arm.
3. cached_surface_package_name memo VALIDATION was added (cross-hit returns
   the pure computation; record counts unchanged) -- REAL hardening of the
   BOOT-20 chain-table family, but NOT sufficient: the package is derived
   from the surface's own (cross-wired) module_name, so the wrong package
   persists. Failing-config verification after that change: still
   1104-1113 unresolved-type errors (4x MirType).

## Next probe (one run): at freeze, eprint for the two optimization_passes
surfaces (and optimizer_manifest): physical_index, canonical_path,
module_name, logical_name, canonical_name, preferred_registry_name, and the
full ordered alias list for their physical indices. That shows whether
admission keyed the lib file's surface under the compiler tree's alias, or
freeze's logical_name re-derivation (module_surface_logical_name_from_path(
surface.canonical_path), module_surface_registry_index.spl:431-433) cross-
assigned canonical_path. Ruled out already: add_indexed_name alias conflicts
(distinct names cannot share an index), canonical-path normalization merging
the two files (paths are textually distinct).

## Freeze-time identity dump + repair pass results (2026-10-13 third pass)

Landed: SIMPLE_HIR_SURFACE_IDENT_DUMP at freeze (prints the per-row LOCAL) +
a post-freeze REPAIR pass re-applying preferred_registry_name from the STORED
rows (pure function of ordered aliases + physical_index), plus
[surface-ident-repair] receipts.

Failing-config run with the repair candidate:
- [surface-ident] dumps: 0 -- every freeze-loop LOCAL row is consistent.
- [surface-ident-repair] receipts: 0 -- every STORED row at freeze end is
  consistent (module_name == preferred, canonical == path-truth).
- Yet the chase-time sibprobe STILL shows the cross-wire
  (facade=compiler.mir_opt.optimization_passes module_name=lib.* package=
  lib.* siblings=2) and the run still fails (~936 unresolved-type, 4x
  MirType -- down from ~1113 after the a804ba111f3 memo validation, so that
  hardening is real but partial).

CONCLUSION: the frozen registry in the dumping process is CLEAN; the chase
reads a DIFFERENT, corrupted surface registry. The HIR phase runs in shard
CHILD PROCESSES (lower_streaming_hir_shard_transaction_v1 -> native_build_
worker.spl), each of which parses its claimed sources and builds its OWN
surface registry in its own process -- that per-process build/copy is where
the cross-wire occurs (matching the run-to-run nondeterminism: which shard
claims the mir_opt files varies with scheduling). The freeze dump must be
re-run INSIDE the shard child (env passes through) to pin whether the smear
is in the child's surface BUILD (admission/merge) or its freeze write-back;
the parent-side data is provably clean.

## Shard-tagged dump result (2026-10-13 fourth pass) — HARD CONTRADICTION

Extended [surface-ident] with a shard tag (SIMPLE_HIR_SHARD_OWNER /
SIMPLE_HIR_SHARD / SIMPLE_PARSE_SHARD / parent) so rows from the parent and
every HIR shard child are attributable, and reran the deterministic failing
config (cold-init, threads=4).

RESULT: 0 [surface-ident] dumps and 0 [surface-ident-repair] receipts across
EVERY process -- the parent AND every shard child's freeze registry is fully
consistent (module_name == preferred, canonical == path-truth for all 2546
surfaces). The SAME run still failed (1260 unresolved-type, 5x MirType) and
the chase-time sibprobe in the same run still shows the cross-wired facade
(compiler.mir_opt.optimization_passes preferred / lib.* module_name+canonical
+package, 2-member sibling bucket).

CONTRADICTION, precisely stated: every frozen registry in every process is
clean; no post-freeze writer exists (grep-verified); ModuleSurface is a class
(array access is by reference, so freeze mutations, the dump, and chase reads
share one row object) -- yet the chase observes a row that exists in NO
clean registry. The chase's facade object therefore originates from a
collection that is NOT any frozen registry and never passes through
module_surfaces_freeze. Candidates for that collection, in order:
1. The chase's `imported_mod` surface is produced by a SURFACE PROJECTION
   (module_surface_declaration_matches / materialization paths build derived
   ModuleSurface values -- e.g. module_surface_explicit_import_origin or the
   compatibility lane at driver_hir_pipeline_lowering.spl:1875) that copies
   fields from TWO different rows (the export-route target's module_name +
   the alias row's preferred name).
2. A walk-local `var surface = ...surfaces[i]` copy under a stage2 aggregate-
   copy miscompile synthesizing mixed rows at COPY time (the copy is clean at
   freeze because the copy happens later).

NEXT PROBE (one run): print the facade's PHYSICAL INDEX and registry identity
in the sibprobe line (facade_mod.physical_index + the row at that index read
fresh from self.module_surfaces), plus whether self.module_surfaces.generation
is 0 (unfrozen) at chase time. That distinguishes 'chase reads the frozen
registry at a cross-written index' from 'chase reads an unfrozen/derived
surface object'. NO fix landed -- the two design candidates (deterministic
shard assignment / parent-snapshot inheritance) both assume the corrupted
object is a shard registry, which this run REFUTES.

## ROOT CAUSE ESCALATION (2026-10-13 fifth pass): stage2 class-aggregate read miscompile

Discriminating probe outcome (b)+(2) combined: the chase-time fresh re-read
`self.module_surfaces.surfaces[871]` returned module_name=lib.compiler.* with
preferred=compiler.* (reg_gen=1, reg_frozen=true) while EVERY freeze-time
observation of the same registry in every process was clean, no post-freeze
writer exists (grep-verified), ModuleSurface is a `class`, and the alias
arrays are conflict-checked. The only remaining explanation: the STAGE2
NATIVE BACKEND MISCOMPILES CLASS-VALUE ARRAY READS (and/or the aggregate
copies around them) -- a slot read intermittently returns identity fields
spliced from an adjacent row (the known 'aggregate copy tag guard' family,
now observed LOAD-side). This is a COMPILER bug in src/compiler aggregate
lowering, not a surface/chase logic bug.

MITIGATION LANDED (this commit): the re-export chase's package-sibling
inference arm now derives the facade package from the registry's SCALAR
ordered alias arrays (surface_registry_name_by_physical_index) instead of
the facade row's identity fields -- class-aggregate reads are avoided on
this path. Failing-config verification: the sibling-arm symptom class is
GONE (the ~1100 'unresolved type' cluster dropped to 0 for that path), but
the build then fails on MOVED instances of the same disease: 'module
compiler.mir_opt.optimizer_manifest has no exported item
manifest_pass_entry_new', 'unresolved name: _pci_ecam_*', and 24x MirType in
c_codegen_adapter/hardware_codegen_types via OTHER row-dependent reads
(export item lists, callable name lists). Whack-a-mole confirms the layer.

THE FIX belongs in the stage2 compiler's aggregate load/copy lowering
(src/compiler 50.mir/70.backend class-value array element access). That
requires: fix at that layer, rebuild stage2 FROM THE SEED (the seed builds
stage2; stage3+ then inherits), and requalify the aggregate-heavy paths
(this bug doc's repro IS the qualification: compiler_cli closure under
cold-init). The SdnValue race (doc sdn_value_enum_race...) plausibly shares
this root cause (nondeterministic cross-module visibility, verifier-only at
first, unexplained by logic review) -- after the aggregate fix lands, rerun
both repros before any further chase/dedup work.

## RESOLUTION LAYER 1 (2026-10-13 sixth pass): the lib.<name> resolver fallback

Re-examining the evidence chain without the miscompile assumption: the chase
reached the facade only when the EXACT-name scalar scan missed in the chasing
process, and module_surface_resolve_absolute_key's UNCONDITIONAL
`candidates.push("lib." + name)` then routed e.g.
compiler.mir_opt.optimization_passes to the src/lib/compiler/mir_opt/
optimization_passes.spl STUB FACADE (same suffix path under the mirror tree),
whose lib.* package bucket (2) instead of compiler.mir_opt (~40) made the
sibling inference miss and memoize the false negative. Every 'impossible'
observation (clean freeze data everywhere, mixed-identity facade, shard and
run nondeterminism) fits a MISSED EXACT LOOKUP + this fallback, no aggregate
miscompile required. (The class-array splice repro built for this cycle was
CLEAN 5x on the buggy candidate -- consistent with NO load-side miscompile.)

FIX LANDED: removed the unconditional lib.<name> / lib.<name>.__init__
candidates from module_surface_resolve_absolute_key; the std.->lib. fold
below is unchanged. A miss now fails LOUD (empty key -> chase-unresolved
receipt) instead of cross-wiring silently.

Failing-config verification (threads=3): unresolved-type 860 -> 715, MirType
4 -> 2. REMAINING failures are now loud misses ('module X has no exported
item Y', unresolved names) -- proving the chasing shard's registry genuinely
lacks modules the chase needs. NEXT (layer 2): shard children must build
COMPLETE registries (full-closure admission) or resolution must consult a
cross-shard authority; the lib. fallback was masking the incompleteness.

## LAYER 2 outcome (2026-10-13 seventh pass): NOT registry incompleteness -- indexed-lookup false negatives

Investigating the loud misses showed the chasing shard's registry was already
complete (the shard child runs the full pipeline; the lib. fallback had been
masking FALSE NEGATIVES from the derived lookup indexes, not absence). The
'module compiler.mir_opt.optimization_passes has no exported item
OptimizationLevel' error fired while the module genuinely DECLARES the item:
surface_declares_item_indexed answered from the per-surface NAMEIDX chain
tables, which false-negative under stage2 (the SAME chain-table corruption
family as the package memo hardened in a804ba111f3).

FIX LANDED: surface_declares_item_indexed now validates a NEGATIVE index
answer against the authoritative six-array linear sweep
(module_surface_declares_item) before returning it; the positive path keeps
the index's speed. Failing-config result: 'has no exported item' cluster
collapses to 2 (from several per run); total unresolved-type fluctuates
715<->786 across runs -- the nondeterministic miss persists in OTHER
unhardened chain-table consumers (surface_decl_owner_indices/PKGIDX,
surface_name_position's other call sites, the reexport memo).

SYSTEMATIC PATTERN (next cycle): every per-surface/per-registry chain-table
index (NAMEIDX, PKGIDX, package memo, reexport_root_memo) needs the same
validate-against-authoritative-sweep hardening, or one shared validated-
lookup helper. The SdnValue race remains unverified against this branch
(budget); its 'items not visible across shards' shape matches indexed-lookup
false negatives exactly.

## CHAIN-TABLE SWEEP (2026-10-13 eighth pass): three more consumers hardened; residual cluster is a DIFFERENT mechanism

Hardened (negative index answers re-checked against the authoritative sweep,
positives keep index speed):
1. register_imported_symbol's NAMEIDX six-probe branch selection
   (module_import_registration.spl) -- a six-miss now re-derives positions
   from the surface's name arrays when module_surface_declares_item is true,
   instead of silently falling into the facade-chase else branch.
2. reexport_root_memo NEGATIVE hits (module_import_registration.spl) -- a
   memoized false negative poisoned every later chase for the key; a
   negative hit now re-walks once and replaces the memo entry on a found
   result (newest-first chain makes the replacement live).
3. surface_decl_owner_indices (module_lowering.spl) -- the
   {text: [i64]} surface_decl_owners Dict (exact BOOT-20 shape) negative
   path now pays the full-registry authoritative sweep it replaced.

Failing-config verification after the sweep: unresolved 786 -> 762, MirType
2, 'has no exported item' 2 -- UNCHANGED in substance. The residual cluster
is PRECISELY IDENTIFIED and is a DIFFERENT mechanism: 717x 'unresolved type:
Option', 448x Result, 307x Dict, 81x 'T', 54x String. 'T' is a GENERIC TYPE
PARAMETER and Option/Result/Dict are prelude/builtin names arriving through
PROJECTED CALLABLE SIGNATURES (parser_type_named_dependencies /
imported_surface_type / materialize_imported_callable_dependency) -- not
surface chain tables. The next investigation target is type-parameter and
builtin-type scoping in cross-module signature projection (the projection
must bind the callee's type params / fall back to prelude builtins in the
IMPORTER's scope). No third band-aid landed without verification, per the
campaign rule.

(Also note: the sweep's reexport-memo negative revalidation makes every
memoized-miss pay one fresh walk -- a deliberate correctness-first cost; if
HIR phase time regresses materially, a per-key per-generation validated
marker is the optimization.)

## COUNTING CORRECTION + TRUE RESIDUAL (2026-10-13 ninth pass)

The origin-trace run (SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1, sweep candidate,
cold-init, threads=3) exposed that ALL prior 'unresolved type' counts in this
doc chain were INFLATED: `grep -c 'unresolved type'` matched the chase-
unresolved advisory's boilerplate ('a later `unresolved type` will be
reported'), not hard errors. The TRUE hard-error count in the same failing
run is 27 [hir-fatal] lines at ~8 sites:

- 4x 'unresolved type: MirType' (transient_owner.spl, hardware_codegen_types,
  verification_codegen_types, +1) -- the original cycle-34 symptom;
- 'unresolved type: ImplBlock' (resolve_lookup_helpers consumer),
  'unresolved type: SymbolId' (interpreter_aop_weave);
- 'module compiler.mir_opt.optimizer_manifest has no exported item
  ManifestPassEntry(ManifestRow)' and 'module compiler.mir_opt.
  optimization_passes has no exported item OptimizationStats' -- persisting
  THROUGH the declares_item_indexed validation, so either the linear sweep
  also misses in that process or the register branch (6-probe fallback)
  still lands wrong;
- one 'module_surface_registry_index.spl:450:13' self-reference (the
  ident-dump line region -- instrumentation artifact candidate).

The 14 hir-unresolved-type-origin trace lines were all 'ImplBlock' with
empty span (synthesized projection). The next probe: per-site eprint of the
surface's actual name arrays for optimizer_manifest/optimization_passes in
the FAILING process (are composite/callable names present?), plus whether
the 'no exported item' sites correlate with the shard that claimed the
module. NO new fix landed this pass (budget); the counting correction
changes the campaign's picture of this bug's size by 30x.

## PER-SITE PROBE OUTCOMES (2026-10-13 tenth pass) — the 27-error endgame discriminated

Instrumented the strict gate (types.spl, [strict-gate] with an authoritative
registry sweep) and the 'no exported item' site (module_import_resolution.spl,
[no-exported-item] with the target surface's six declaration-array counts).
One instrumented failing-config run: 11 hir-fatal (subset of the 27 fired this
run -- nondeterministic subset).

OUTCOME (c) for 'unresolved type: MirType' and 'ImplBlock': the declaring
surface IS present in the chasing process (reg_surfaces=2564, complete) and
DOES declare the name (decl_count=1, decl_first=compiler.mir.mir_types /
compiler.traits.trait_impl). The disease is NOT absence and NOT the registry
chain tables: the declared type never gets BOUND into the consumer's symbol
scope through the materialize -> register_imported_symbol ->
bind_qualified_type chain (the symbol-table qualified dicts are the remaining
BOOT-20 surface). Next fix target: validate/ repair that binding (or have
imported_surface_type's fall-through bind directly from the unique declaring
surface when decl_count==1).

OUTCOME (b) for 'no exported item': [no-exported-item] module=
compiler.mir_opt.optimization_passes resolved=compiler.mir_opt.optimization_
passes surf_module=lib.compiler.mir_opt.optimization_passes surf_idx=871 with
ALL SIX declaration arrays = 0. The registry's name->index map routes the
COMPILER name to the LIB FACADE's surface. Root: an admitted source row
carries the facade's path with the impl's logical name (dual-tree import
resolution admitted src/lib/compiler/mir_opt/optimization_passes.spl AS
compiler.mir_opt.optimization_passes), and alias admission trusted the row's
module_name without checking it against the path derivation. Next fix (pure
admission validation, no chase change): in add_alias_canonical_identity and
add_parsed_canonical, REJECT a row whose module_name disagrees with
module_surface_logical_name_from_path(canonical_path) (fold-std compared) --
legit authored/snapshot aliases of one file derive the same logical name, so
the check only kills mis-tagged rows; loud Err, no silent cross-map.

No fix landed this pass (budget exhausted after the probe rebuild+run); both
fixes are specified above with their evidence.

## Cycle 38 (2026-10-13): both fixes landed; FIX 1 reconciled against the numbered-path spec

FIX 2 (outcome c) implemented in
`imported_surface_type` (src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl):
after the qualified raw lookup under the callable owner's module fails, an
authoritative singleton-declarer sweep (`surface_decl_owner_indices`, the
chain-table-hardened index from cycle-36) runs; when EXACTLY ONE surface
declares the name, the declaring surface is materialized into this importer's
symbol table exactly as `materialize_imported_callable_declared_dependency`
does it (qualified local `{owner}::{name}`, `register_imported_symbol`,
`bind_qualified_type` under the owner's own module name), the raw lookup is
retried under that same qualifier, and only a still-missing symbol falls
through to the historical `named_instance_kind_or_any` path. Env-gate-free but
conservative: fires only on initial-lookup failure AND decl_count == 1.

FIX 1 (outcome b) reconciled: the derivation check SURVIVES only in the
canonical lane (`add_surface_canonical_identity`, a NEW physical source, whose
first spelling is path-derived by construction). The alias-lane check was
REMOVED before it ever shipped: `module_surface_numbered_path_spec.spl` pins
derivation-divergent alias names as legal (`std.editor.alias_types` admitted
for the `types.spl` path; fold-std derivation `lib.editor.alias_types` --
spec example "keeps one physical editor owner through construction and freeze"
failed 1/4 with the check in, passes 4/4 with it out). The entry-closure
dual-tree import walk depends on the same shape: a lib-tree file walked under
a compiler.* import spelling registers (facade path, compiler name) alias rows
by design (`_driver_collect_entry_import_source_untimed` name list). The
cycle-37 cross-map row (facade path + compiler.mir_opt.optimization_passes) is
registry-indistinguishable from those legal rows, so the doc's premise "legit
aliases derive the same logical name" is falsified for the alias lane: no
registry-local derivation check can kill the bad row without also killing the
spec'd behavior. The durable fix for the no-exported-item class belongs at the
closure/inventory selection layer (prefer the impl tree over an all-zero stub
facade when both twins exist), recorded here as the next target.

Verification this cycle (seed interpreter, worktree): numbered-path spec
4/4 PASS; `callable_dependency_frozen_alias_retry_spec` 6/6 PASS;
`callable_signature_owner_imports_dependency_spec` 4/4 FAIL observed BOTH with
and without these edits -- pre-existing at branch tip b163025ac1f, not a
regression from this change.

### Cycle-38 verification results (candidate build/mirtype/stage2-endgame/simple, commit 6197f707a20)

Failing config (compiler_cli closure, SIMPLE_SCV_INVENTORY_COLD_INIT=1, threads=3,
fresh cache): 6 hir-fatal, DOWN from 27 (branch-tip baseline b163025ac1f). All 6
are the no-exported-item/unresolved-name facade class; the unresolved-TYPE class
(FIX 2's target -- MirType, ImplBlock, and the SdnValue/Float family) is GONE:

- module compiler.mir_opt.optimizer_manifest has no exported item OptimizerManifest (idx 2183)
- module compiler.mir_opt.optimizer_manifest has no exported item manifest_pass_entry_new (idx 2415)
- module compiler.mir_opt.optimization_passes has no exported item optimize_syscall_batch (idx 871)
- unresolved name: optimize_syscall_batch (60.mir, consequence of the idx-871 routing)
- unresolved name: rt_env_get in 20.hir (pre-existing: also in cli-persite/cli-libfix logs)
- unresolved name: _pci_ecam_base at :0:0 in pci.spl (synthesized span; pre-existing class)

The first three are the FIX-1-target class: the registry still routes compiler.*
names to lib.* stub facades. The warm-inventory run (cold-init unset, fresh
cache) reproduces the IDENTICAL 6 errors -- the residual is now deterministic,
not the old nondeterministic subset.

test_runner closure (cold-init, threads=3, fresh caches), SdnValue triple
(`undefined variable SdnValue|multiple wildcard|unresolved method call: Float`),
3 runs: 0 / 0 / 0. The SdnValue/Float family is fixed by FIX 2.

unit specs (seed interpreter): module_surface_numbered_path_spec 4/4 PASS;
callable_dependency_frozen_alias_retry_spec 6/6 PASS;
callable_signature_owner_imports_dependency_spec 4/4 FAIL both with and without
this change (pre-existing at b163025ac1f, verified via stash).

Gate status: hir-fatal 6, NOT 0. The remaining frontier is the facade-routing
class only; next fix target is the closure/inventory selection layer (prefer
the impl tree over an all-zero stub facade when dual-tree twins exist), as
recorded above. FIX 1's original alias-lane admission check would not have
helped: the bad row is registry-indistinguishable from spec-legal alias rows.

## Cycle 39 (2026-10-14): facade-routing frontier fixed at the closure selection layer — hir-fatal 6 -> 0

Root cause (found by tracing the admitted-row factory, not the registry): the
declared-source-roots resolver `_driver_resolve_source_root_entry_import_v1`
physically walks src/lib before the numbered compiler layout, so
`compiler.mir_opt.<name>` resolved to the 11-line src/lib stub facade; the
phase-1 closure loop (driver_source_pipeline_loading.spl) then SYNTHESIZED an
alias row tagging the ZERO-declaration facade with the compiler name (the
`if not closure_has_exact` fallback). That row, not any admission-lane
validation gap, produced the registry cross-map (surfaces idx 871/2183/2415).
Cycle-38's hypothesis (admission validation) was therefore unfixable by
construction, as the numbered-path spec had already hinted: the bad row and
spec-legal alias rows are identical in shape.

Fix (two coordinated layers, commit 14c7986dd16 on fix/mirtype-facade-selection-20261014):
1. `_driver_numbered_compiler_candidates_v1`: added parent layout
   `compiler/60.mir_opt` as a second candidate for `compiler.mir_opt.*`
   (optimization_passes, optimizer_manifest, optimizer_plugin,
   optimizer_kernel_contract, mir_opt_integration and the _OptimizationPasses
   part package exist ONLY at parent level; nested `mir_opt/mir_opt` stays
   first — the two levels share no file names, so every currently-resolving
   first-hit is preserved).
2. Phase-1 closure loop: when the selected file's NATIVE names lack the import
   spelling, retry `_driver_resolve_entry_import` and prefer a file that
   natively owns the spelling, before falling back to the synthesized alias
   row. Genuine relative imports (no native owner) are unchanged.

Residual hard errors in the same gate, also fixed in 14c7986dd16:
- `module_surface_registry_index.spl:450` — the cycle-35/36 surface-ident
  probe used raw `rt_env_get`, which the self-hosted HIR cannot resolve in
  that module ('unresolved name: rt_env_get'); switched to the
  std.nogc_sync_mut.io_runtime `env_get_opt` facade (also satisfies the
  direct-env-runtime-guard).
- `src/os/drivers/pci/pci.spl` — `_pci_ecam_base` (cfg arm64 0x4010000000 /
  riscv64 0x30000000) was dropped by the x86-port-io consolidation while its
  two @cfg call sites remained; restored from 6f86ff32a7d~1.

Verification (candidate build/mirtype/stage2-owner/simple, failing config
SIMPLE_SCV_INVENTORY_COLD_INIT=1 threads=3, fresh caches):
- cli-owner.log (before the residual fixes): hir-fatal 6 -> 2, both remaining
  pre-existing (rt_env_get, _pci_ecam_base). Facade class fully gone.
- cli-owner2.log (after all fixes): hir-fatal = 0; HIR completes 2564/2564
  failed=0; the build proceeds PAST HIR through the any-escape pass (1598
  E-MC-ANY warnings, non-fatal) and the enum-contract pass (0 diagnostics),
  then the process dies SILENTLY with no diagnostics — suspected OOM (host at
  91/121 GB with campaign cycle 37 running concurrently); the next frontier
  (MIR codegen / link) was not reached. Not yet classified OOM vs crash.
- test_runner closure 3x (fresh caches): SdnValue triple 0/0/0, hir-fatal 0
  in every run.
- Specs: module_surface_numbered_path 4/4, callable_dependency_frozen_alias_retry 6/6.
- Warm-inventory regression: cli-owner-warm.log FAILED INSTANTLY at SCV
  admission ('SCV-E-ADMISSION: compile-event-journal-missing (first build in
  this checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)') -- one log
  line, before parse/HIR. This is a worktree admission-state artifact, not a
  code regression: the compile-event journal covers generation 23 @ git head
  6197f707a20; the cycle-39 commits moved the git head, so the warm route
  demands a journal entry that only a cold-init run would publish. It does not
  exercise any changed code. Cycle-38's warm run passed on the same script when
  the journal state was consistent, and every cycle-39 cold run is clean.

Open follow-ups: (a) rerun the failing config on a quiet host to classify the
post-enum-contract silent death and capture the next frontier; (b) the same
doubled-mapping pattern exists for compiler.blocks (15.blocks parent files
vs 15.blocks/blocks) but no lib stubs shadow it in the current closure —
left untouched; (c) the canonical-lane derivation check from cycle 38 rejects
out-of-tree probe entries (test/_probe_root_tmp) — cosmetic for probes only.
