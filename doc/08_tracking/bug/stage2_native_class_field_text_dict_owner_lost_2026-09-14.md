# Stage-2 native codegen: `imported enum has no declaration owner` on a plain single-hop import
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-14)
- Lane: BOOT-20 (`work/bootstrap-s3-2-2026-09-14`)
- Binary: pinned Stage-2 candidate `bin/release/aarch64-unknown-linux-gnu/simple.phase2`
  (the boot18d `stage2/aarch64-unknown-linux-gnu/simple` artifact), sha256 `80911c47f07cdb64...`
  (short form used throughout the BOOT-18/19/20 lanes: `80911c47f07cdb64b4c3`)
- Class: native-codegen-only miscompile (Dict class field), workaround landed
  in `be66529a5f3` (`fix(hir): read imported enum owner from the symbol table,
  not a native-buggy class field`)

## Symptom

Receipt-free Stage 3 (`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
<stage2-candidate> native-build src/app/cli/bootstrap_main.spl ...`) fails
HIR lowering with:

```
error: focused native-build: HIR lowering error in src/app/cli/bootstrap_main.spl:
imported enum `EnumPatternPayload` / `DiagramGraphKind` / `CompileMode` /
`MarkdownBlock` / `UnaryOp` has no declaration owner
```

## Minimal reduction (measured 2026-09-14, ~1s native-build each)

Two files, no facade, no re-export, no sibling directory interference, enum
never even referenced in the importer's body:

`a.spl`:
```
enum Kind:
    Alpha
    Beta
```

`c.spl`:
```
use pkg.a.{Kind}

fn main():
    print("hi")
```

`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 <stage2-candidate>
native-build c.spl -o out` fails:
`imported enum \`Kind\` has no declaration owner`, attributed to BOTH `c.spl`
and (when a re-export facade is inserted) the facade module itself.

Removing the facade, removing the match/usage of the enum, and moving the two
files into separate directories (to rule out directory-sibling
reprocessing, `resolve_package_sibling_symbols`) all leave the failure
unchanged. This is **not** a re-export-chase defect — the
`[hir-reexport-chase-unresolved]` lines that appear alongside it in the
Stage-3 log (chasing unrelated builtins through `std.nogc_sync_mut.spec`'s
facade chain, see the companion doc below) are unrelated noise for this
specific error.

## Discriminated: native-only, not a `.spl` logic bug

The exact same shape, run through the SAME `.spl` HIR-lowering source
in-process (calling `compiler.hir.hir_lowering.types.hirlowering_for_module`
+ `.lower_module(...)` directly, the technique
`test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl`
already uses), interpreted by the Rust seed via `bin/simple run`:

```
errors.len=0
imported_enums.len=1
imported_enum_owners.len=1
```

Clean. Same logic, different engine (interpreted vs. natively compiled),
different result. (An earlier attempt to reproduce this in-process failed
with `missing importing module surface for boot20.consumer` — that was a
harness bug: the harness omitted the consumer module's own entry from the
`modules`/`sources` maps passed to `module_surfaces_from_modules`. Once the
consumer module is registered too, the fixture lowers clean. Anyone
re-chasing this: don't rediscover that dead end.)

## Root cause

`src/compiler/20.hir/hir_lowering/_Items/module_build.spl`,
`lower_module_enum_definitions` (pre-fix, ~line 165-178), reads the enum's
declaring-module name from `self.imported_enum_owners`, a
`{text: text}` (`Dict<text,text>`) **class field** of `HirLowering`,
written at `module_import_registration.spl:373`
(`self.imported_enum_owners[local_name] = imported_mod.module_name`) in the
same guarded block that writes the companion `imported_enums` field. Under
Stage-2 native codegen, this field's `contains_key`/bracket-read pair
silently misreports for this shape — the value was written, but the read
back does not see it (or sees corrupted data). Confirmed independently
(outside the compiler entirely) with a minimal probe:

```simple
struct EnumLike:
    tag: text

class Holder:
    enums: {text: EnumLike}
    owners: {text: text}

fn main():
    var h = Holder(enums: {}, owners: {})
    val k = "Kind"
    if not h.enums.contains_key(k):
        h.enums[k] = EnumLike(tag: "enum-payload")
        h.owners[k] = "mod_a"
    print("OWNER-PRESENT: " + h.owners[k])
```

Native-built by the Stage-2 candidate and run: prints
`OWNER-PRESENT: 200191203302897` — a raw undecoded word, not the text
`"mod_a"`. `contains_key` itself reports correctly (`true`) in this exact
probe; it is specifically the **bracket-read of a `text`-valued CLASS FIELD
Dict** that is corrupt. This is a new variant not covered by
`doc/07_guide/language/dict_native_pitfalls.md`'s existing truth table
(which documents array-valued class-field bracket-read SEGVs, not
text-valued garbage reads on a hit).

A related but distinct native defect in the same family: moving the
write (`self.<dict>[k] = v` inside a guarded `if` block) into a class
**method** — rather than inline in `fn main()` — makes the Stage-2
candidate **SEGV while compiling** the probe program (during its own MIR
lowering), even for a SINGLE dict-field write, not just the dual
enums+owners write. See the companion bug doc
`stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14.md`.

## Fix (workaround, not a root-cause fix)

`imported_enum_owners` is never read again for this decision.
`lower_module_enum_definitions` now calls a new helper,
`imported_enum_owner_module(local_name)`, that reads the owner back from
`HirSymbol.defining_module` — already recorded at the exact same
registration call site
(`self.symbols.define(local_name, SymbolKind.Enum, ..., Some(imported_mod.module_name))`)
— using the scalar-safe `lookup_or_invalid` -> `self.symbols.symbols.has(id)`
-> bracket-read -> `?? ""` pattern `claim_materialized_payload_binding`
already relies on for exactly this class of native Dict hazard.
`imported_enum_owners` the field, its write, and its per-module reset are
all left in place (unused for this decision) because two other specs pin
its literal source shape and reset contract:
`test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl`
and `test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl`.
Deleting the field would need updating both; reading around the bug instead
touches only the one call site that was actually broken.

Landed: `be66529a5f3` (`fix(hir): read imported enum owner from the symbol
table, not a native-buggy class field`), `work/bootstrap-s3-2-2026-09-14`.

## Verification

- RED (pre-fix): `SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
  <old stage2 candidate, sha 80911c47f07cdb64b4c3> native-build c.spl -o out`
  → `imported enum \`Kind\` has no declaration owner`.
- GREEN (seed, contract pin): `test/01_unit/compiler/hir/imported_enum_owner_native_workaround_spec.spl`
  passes under `bin/simple test` (interpreted).
- GREEN (native, post-fix): pending a rebuilt Stage-2 candidate from this
  fix — see the BOOT-20 receipt for the rebuild outcome.

## Related

- `doc/08_tracking/bug/phase2_stage2_spec_framework_unresolved_reexport_chase_2026-09-13.md`
  — a DIFFERENT root cause (multi-hop re-export chase through
  `std.nogc_sync_mut.spec`), filed by a sibling lane; do not conflate the two.
  That doc's own recommendation ("reproduce narrowly with a 3-file minimal
  facade chain... to isolate whether the break is at the enum-import step
  specifically or the generic multi-hop facade chase") is answered by this
  doc: it is neither — it is a native Dict class-field defect, present even
  with zero facade hops.
- `doc/07_guide/language/dict_native_pitfalls.md` — existing truth table;
  this bug is a new row (class-field `text`-valued bracket-read garbage on a
  hit), not yet added there pending wider confirmation.


## Addendum 2026-09-17 (bootstrap-unblock lane, do not overwrite)

Full-bootstrap chain13 reached Stage 3 with this class live. Findings:

- Repro harness: run the chain-admitted stage2 binary
  (`.simple/storage/build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple`)
  with the exact stage3 env replayed from
  `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage3-command.transcript`
  (source the explicit-env lines; point the four cache/profile paths at a
  scratch dir). Plain hand-picked env passes (884/884); the exact env
  reproduces 36 `imported enum has no declaration owner` + `unresolved type`
  fatals + a terminal SIGSEGV. `MALLOC_ARENA_MAX=2`/`MALLOC_TRIM_THRESHOLD_=0`
  are NOT the trigger (failures persist with them unset) — the exposing
  variable is elsewhere in the engine env (candidates: SIMPLE_BOOTSTRAP_STAGE3,
  SIMPLE_STAGE3_STREAMING_SURFACES, SIMPLE_PACKAGE_INDEX_COLD_INIT,
  SIMPLE_NATIVE_ARENA_DECLS; not yet bisected further).
- Fixed and merged (PR #1052): the enum-owner read via a parallel `[text]`
  rows mirror (house-safe structure) — 36/36 owner errors eliminated; the
  legacy dict path never engaged in verification.
- Remaining: `unresolved type: SccPublicationOwnershipV1 /
  DemandCompileCountersV1 / DemandCompileExecutionV1 / RouteCapabilityScope`
  attributed to driver.spl / driver_aot_output.spl / driver_pipeline.spl
  (spans empty). These route through glob imports
  (`use compiler.driver.driver_pipeline_execution.*`) whose re-export chase
  walks `self.module_surfaces.surfaces` — a HirLowering class-field subject to
  the documented "native cross-module frame sync can restore an older visit
  snapshot" hazard (module_import_registration.spl:783). The root memo
  (`reexport_root_memo_index`) is also a HirLowering field and negative
  results are memoized permanently per generation.
- `SIMPLE_REXMEMO_VERIFY=1` (the in-code memo self-check) SEGFAULTS under the
  exact env — evidence the walk/recursion itself is corrupted, not just the
  memo.
- Candidate fix (UNVERIFIED, stashed in the bootstrap-lane session, NOT
  merged): `module_surface_export_origin_index_position` in
  module_surface_types.spl — its scalar-array scan fallback was unreachable
  (`index_by_name.len() >= 0` is always true); made the dict fast path
  validated + scan-on-miss. Did not cure the unresolved-type class (the
  failing routes are not origin-index arms) and the verify run segfaulted
  before a clean measurement.
- Localization knobs that exist and work: SIMPLE_HIR_ENUM_OWNER_TRACE=1,
  SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1, SIMPLE_BOOTSTRAP_DIAG=1
  (`[reexport-chase] mod=... wanted=... imports=N exports=M found=F`),
  SIMPLE_REXMEMO_VERIFY=1 (crashes).

### Addendum 2026-09-17 (second pass) — env-bisect results and mechanism analysis

Falsified as the exposing trigger, each with a full exact-env replay minus one
variable (25-min runs):
- `MALLOC_ARENA_MAX=2` / `MALLOC_TRIM_THRESHOLD_=0` unset: same fatals + SIGSEGV.
- `SIMPLE_STAGE3_STREAMING_SURFACES` unset: still fails; the failing TYPE SET
  CHANGES with the perturbation (BuildLinkState / BuildProgressState vs the
  original SccPublicationOwnershipV1 / DemandCompileExecutionV1 /
  RouteCapabilityScope). A failure set that shifts with heap layout/timing
  perturbation is the signature of reading uninitialized or stale memory, not
  of one wrong branch.

Mechanism analysis (from reading the walk + registry code):
- The unresolved types route through glob imports whose re-export chase walks
  `self.module_surfaces.surfaces` (a HirLowering class field). The code
  documents the hazard itself (module_import_registration.spl:783): HirLowering
  fields are shared by nested root queries and "native cross-module frame sync
  can restore an older visit snapshot after a nested call returns". If a late
  surface registration is reverted by such a restore, the generation guard
  (read from the same restored field) cannot detect the loss, and memoized
  negatives become permanent -- self-consistent within the stale snapshot.
- The per-surface route arrays are populated before streaming release and the
  code asserts "promoted field owners remain valid"; the SoA promotion path
  (driver_source_pipeline_parsing.spl) is the right place to audit first for
  any array that still aliases released per-file records.
- `SIMPLE_REXMEMO_VERIFY=1` (the memo self-check) SIGSEGVs under the exact env,
  so the walk itself cannot currently be trusted to re-verify its own cache.

Conclusion: the remaining stage3 blocker is a native-codegen memory-safety
defect (stale/uninitialized reads under nested calls) in the pure-Simple
compiler, larger than the dict-membership class fixed in PR #1052. The
house-documented mitigations (fresh carriers, accessor-only fields, scalar
mirrors) are the right pattern for any further source hardening; a codegen fix
needs the BOOT-20 owner lane.

## 2026-09-17 follow-up: full-chain reproduction + origin-index hardening (branch fix/boot20-surface-index)

Full bootstrap chain on current main (all prior workarounds in place:
02d5b7c1405 enum-owner-via-symbol-table, 12902e1c65b surface-index linear scan,
#1052 rows mirror, #1044 receiver/closure-context): Stage 2 PASS (890/890),
Stage 3 FAIL exit 1. Failure signature CHANGED from the 36-error enum-owner
slice to a broad builtin-name collapse:
- 15,876 `unresolved type` + 15,538 `unresolved name` (capped ~10/file),
  dominated by `text` (4,085), `i64`, `bool`, `Option`, `Dict`, `Result` and
  the int widths -- i.e. the prelude itself stops resolving across most of
  the closure, plus genuine receipt types (SccPublicationOwnershipV1,
  DemandCompile*V1, RouteCapabilityScope) in 80.driver.
- 15,361 `[hir-reexport-chase-unresolved]` receipts: the re-export chase
  returns not-found for names the facades genuinely route. `local=` is bare
  (`text local=text`, 4,085x) for misses and qualified
  (`local=lib.nogc_sync_mut.io_runtime::Option`, 171x) for the
  terminal-register path -- the two populations are distinct.

New defect sites confirmed (all the documented `{text:*}` class-field Dict
class), fixed on this branch:
1. `module_surface_export_origin_index_position` (module_surface_types.spl):
   the `index_by_name.len() >= 0` gate is constant-true, so the Dict path ran
   unconditionally and the scalar-array fallback was DEAD CODE. A false
   contains_key negative returned -1 (origin arm of the chase misses). Fixed:
   scan the retained `names` array; Dict no longer consulted.
2. `module_surface_export_origin_index_put` (same file): slot lookup was
   `index_by_name.contains_key` + bracket-read. False negative -> duplicate
   `names` entry; false positive -> `owner_modules[garbage]` OOB write. Fixed:
   locate the slot by scanning `names`; arrays are the authority.
3. Sibling-inference predicate (module_surface_export_index.spl:573) read
   `owner.export_origins.contains_key(source_name)` (the `{text:
   ModuleSurfaceExportOrigin}` class-field Dict). Fixed: reuse the hardened
   position scan.

Seed-interpreter spec validation of the three edits: origin/chase/surface
specs PASS (export_origin_layered_facade, bare_export_facade_chain_reexport,
hir_package_dependency_scan_memo 7/7, standalone_module 2/2,
hir_lowering_items_surface_completeness, imported_enum_owner_native_workaround);
the four FAILs (explicit_import_beats_glob_reexport,
hir_unresolved_name_import_reachability, module_surface_index_allocation_guard
0/2, resolve_import_symbols 1/32) are pre-existing on clean main (A/B via
stash confirmed) -- not regressions.

Remaining suspects if Stage 3 still fails after this slice (from static
reading, in order of likelihood):
- `reexport_root_memo_item` (`{text: text}`) is read UNGUARDED at
  module_import_registration.spl:780 after an index-dict hit; corruption-on-hit
  feeds a garbage `item_name` straight into `register_imported_symbol`. The
  index dict (`{text: i64}`) false-NEGATIVES per the surface-index finding, so
  it is retry-safe; the item dict is not.
- `surface_decl_owner_indices` (module_lowering.spl:427) ambient-probe
  `surface_decl_owners` `{text: [i64]}` contains_key -> `[]` on a false
  miss, failing the unique-owner check for names like `Option`.
- `SIMPLE_REXMEMO_VERIFY=1` SIGSEGV under the exact env (documented above)
  still blocks memo self-verification.
