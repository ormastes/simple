# Phase-2 verification matrix: strict stage-2 compiler error family (2026-10-09)

Batch record for the phase-2 verification matrix failures of the self-hosted
(stage-2) compiler on worktree `release-llvm-20261007` (branch
`work/rel-phase2-matrix-fixes-20261009`, stage2-admitted compiler sha
`17133b7019…`, snapshot `scv-revision-v1-cbb5b270…` == src/ at the time).

Evidence logs:
`.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/test_runner_build.log`
and `compiler_cli_build.log`.

Local reproducers live under `build/matrix-probes/` (gitignored, kept for the
compiler lane). Seed = `src/compiler_rust/target/bootstrap/simple` (accepts
every construct below; verified by running the probe programs where the
construct is runnable). Stage-2 = the admitted stage2 binary.

## Source bugs fixed in this batch

### S1. Bare enum variant `Composite` in test-runner matches (error classes 3, 4, 5)

- **Errors**: `enum match: bare variant 'Composite' is ambiguous (declared in
  multiple enums)` (5x), paired 1:1 with `enum construction: missing runtime
  identity for ''` (5x) and with `unresolved method call: contains` /
  `find` at `test_runner_types.spl:8:38` (bogus span; real sites are the
  `spec.contains(layer)` / `spec.find("(")` arms).
- **Root cause (source)**: five match arms used the bare variant
  `case Composite(spec):` in a build where several enums declare `Composite`
  (`lib/*/compositor/frame.spl`, `lib/*/message_transfer.spl`, plus
  `TestExecutionMode` itself). The strict compiler rejects the ambiguity; the
  failed pattern leaves the `spec` binding untyped, which cascades into the
  `contains`/`find` "unresolved method" errors, and the enum-construction
  identity errors pair with the same five sites.
- **Fix**: qualify all bare arms as `TestExecutionMode.Composite(...)`:
  - `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:460,470,476,494,511`
  - `src/app/test_runner_new/test_runner_types.spl:192,202,208,226,243`
  (Sibling modules `test_runner_config.spl` / `test_runner_files.spl` already
  use the qualified form — this matches the established style.)
- **Validation**: stage-2 now lowers a probe copy of the fixed module with
  zero MIR errors (previously reproduced `contains`/`find` at the phantom
  8:38 span); seed runs both modified modules correctly
  (`build/matrix-probes/seed_check_types.spl`, `seed_check_app_types.spl`
  print OK). Repro pair: `build/matrix-probes/p7/main.spl` (`f` qualified
  passes, `f2` bare fails).

## Compiler bugs (NOT patched in source; reproducers in build/matrix-probes/)

### C1. Unresolved primitive text methods on non-trivial receivers (error class 1, and `trim`)

`to_int`, `contains`, `find`, `lower`, `trim_start`, `last_index_of`,
`split`, `trim` fail MIR method resolution when the receiver is not a plain
local val:
- array index: `args[i].to_int()` — `p3c.spl` (stage-2 errors; seed runs it,
  prints RESULT=3).
- field of an imported struct (`C2` family below).
- nil-guarded `text?` receiver: `env_env.lower()/trim` at
  `src/app/io/mod.spl:123` (cranelift-matrix data point; same family as the
  recently landed `f87ed657830` / `cb2bed7ddff` narrow-nil-receiver fixes, so
  the admitted compiler still misses some receiver forms).
Error spans are misattributed (e.g. every `to_int` in
`test_runner_args.spl` is reported at `57:8`, a fn-declaration line).

### C2. Enum / struct equality through IMPORTED struct fields (error class 2)

`r.packet.packet_kind != KindV4.Frozen` fails with "operator overload for
struct KindV4" when `Receipt`/`Packet` come from an imported module
(`p6/t1.spl`, `t2`, `t4`, `t6`, `t8`, `t10`, `t11`, `t14` fail), while the
identical code with a LOCALLY declared struct passes (`p6/t12`, `xmod`
probes). Bare enum parameters compare fine (`p6/t5.spl`). This is the root of
the `ProcessObservationPacketKindV4` errors at
`src/lib/nogc_sync_mut/io/process_ops.spl:1096,1119` (reproduced via
`build/matrix-probes/pb/` copy of the real module) and of the whole
`WalEntryType` / `TerminationCause` / `BlockStatus` / `FeatureStatus` /
`DecisionStatus` / `ResourceEvidenceQuality` / `McdcMode` operator-overload
error family in the matrix log.

### C3. Generic type parameter named `Id` is not resolved (CLI HIR failure, module 1 of 2)

`lib.common.search.ranking` + `lib.common.search.types` poisoned with
`unresolved type: Id` where `Id` is the type parameter of
`struct PostingList<Id>`. Minimal repro: `p10_generic.spl` / `p10b.spl`
(stage-2 HIR rejects; seed runs fine). Renaming the parameter to `T` passes
HIR (`p10c.spl`), so the strict type table mishandles the name `Id`
specifically.

### C4. CLI HIR failure, module 2 of 2: `compiler.backend.backend.backend_types`

`unresolved type: BackendKind` reported inside the very file that declares
`enum BackendKind` (line 22). Not reproduced standalone (needs the large CLI
closure); the module is poisoned wholesale in the module-diagnostics sweep
(attempt `…/module-diagnostics/attempt.sLaYUC/36`). Treat as a strict-HIR
module-registration bug pending a minimal repro.

### C5. Diagnostic-storm "hang" on the error path

The cranelift-observed "100% CPU after printing a MIR error" reproduces on
the llvm lane as pathological slowdown, not an infinite loop: per-module
diagnostics attempt 36 (`src/app/bootstrap_builder/main.spl --emit-object`)
ran 1489 s at 100% CPU and exited FAIL, emitting a 43 MB log dominated by
`hir-reexport-chase-unresolved` lines (quadratic in closure size; 118k lines
for one module). Small closure repro of the spam multiplier:
`build/matrix-probes/p5_process_ops.spl` (tiny entry, dozens of chase lines).
Seed has no equivalent pass. Suspect: the chase-unresolved diagnostics loop;
needs a compiler-lane fix (cap/dedup), not a source change.

## Remaining unknowns

- **B5b "match has multiple wildcard/binding default arms"** (3 unique sites):
  no match in any failing source actually has two wildcard/binding default
  arms (scanned all runner modules cited in the log). Likely a cascade of the
  bare-variant/identity failure path in the same module cluster (it sits
  inside the `test_runner_types` error group), but it was NOT reproduced
  standalone — the small-closure copy of the module emits only the
  contains/find errors. Needs re-check after the S1 fix lands in a full
  matrix run.
- The `for-in over non-array iterables (collection mir type: I64)` family
  (e.g. `test_runner_args.spl:761` `for i in s.len():`) and the
  `unresolved method call: set/get/valid_rows/…`, `infer-arm`, and
  `enum match: unsupported arm pattern` masses in the same logs were not
  bisected in this batch; several are likely C1/C2 cascades but that is
  unproven.

## 2026-10-11 addendum: valid_rows / for-in I64 family bisected (release-llvm-20261011 lane)

The previously unbisected `for-in over non-array iterables (collection mir type:
I64)` + `unresolved method call: valid_rows` family is a C1 receiver-identity
cascade: in `database_queries.spl` and `factory.spl` the table receiver is a
`case Some(table):` match-arm binding from `SdnTable?`. Strict HIR fails to
propagate the arm payload type, `SdnTable.valid_rows() -> [SdnRow]`
(core.spl:408) fails to resolve, and the fallback names a same-shaped `i64`
symbol — the unrelated `valid_rows: i64` parameter in
`src/lib/gc_async_mut/slang/model_executor/backend.spl:742,767` — so the for-in
collection lowers as I64. Paired `enum match: unsupported arm pattern` is the
same arm-pattern typing failure.

Workaround landed on `work/release-llvm-fixes-20261011` (PR #2999): bind match
results and arm payloads to explicitly annotated `SdnTable` locals before
calling `valid_rows()`. Probes for re-verification:
`build/matrix-probes/dbq/` (minimal MiniDb repro + annotated-local variant) and
`build/matrix-probes/c4_backendkind/`. Compiler-side fix still required for the
receiver-identity family itself; PR #2967 (HIR cache/receiver identity,
e650ad19d67) may cover part of it.

## 2026-10-11 addendum 2: std.crypto.sha3 module-index registration gap (C6, release-llvm-20261011 lane)

Stage-2 matrix `test_runner_build` (admitted compiler 85fc943a, post-PR-#2967)
fails in `src/lib/common/crypto/hmac.spl`:

    module std.crypto.sha3 has no exported item sha3_384_bytes
    module std.crypto.sha3 has no exported item sha3_512_bytes
    unresolved name: sha3_256_bytes / sha3_384_bytes / sha3_512_bytes
    (12 errors; module lib.common.crypto.hmac poisoned)

The functions ARE declared in `src/lib/common/crypto/sha3.spl:341,347,353` with
the same plain `fn` style as `sha1.spl:251` (`sha1_bytes`), which imports fine.
So the compiler's module-index registration silently drops std.crypto.sha3's
exports. Same family PR #2967 chased ("failed one HMAC module importing SHA3
functions; module-index registration under investigation") but the failure
persists WITH #2967 merged (e650ad19d67 in tree). Suspect visit/declaration
order sensitivity (cf. robust-5a test 2b284af6820 pinning module typing
against declaration/name/visit order). Needs a compiler-lane fix; probes under
`build/matrix-probes/sha3reg/`.

## 2026-10-11 addendum 3: C6 root cause — missing std.crypto.sha3 facade (source gap, not a registration bug)

Bisect (probes `build/matrix-probes/sha3reg/`, minimal-shard-repro) corrected
addendum 2: `std.crypto.sha3`'s exports are NOT dropped by a registration bug.
`src/lib/crypto.spl` declares `mod crypto.types/sha256/sha512/hmac/legacy_hash/
sha1` but no `mod crypto.sha3`, and `src/lib/crypto/sha3.spl` did not exist —
sha3 was the only `common/crypto` module missing its `src/lib/crypto/*`
re-export facade. The sequential compile path falls back to the real file, so
only the `--low-memory` HIR-shard path (used by the stage-2 matrix builds)
fails: item lookup chases facade `lib.crypto`, which declares no sha3 names.

Fix (PR on work/rel-c6-sha3-facade-20261011): add `src/lib/crypto/sha3.spl`
re-export facade + `mod crypto.sha3` in src/lib/crypto.spl (matches the
`crypto/hmac.spl` idiom; validated 0 hir-fatal on a 256-module shard repro).

Latent same-family gaps (NOT in today's closures; fix when imported):
`std.crypto.md5` (src/os/crypto/pbkdf1.spl:15) and
`std.crypto.entropy_platform` (src/os/crypto/entropy.spl:5) also lack
`src/lib/crypto/*` facades.

Related open infra failure (NOT source): `compiler_cli_build` shard owner went
`status=BLOCKED exit=-2 claimed=0 sealed=-1 inventory incomplete rows=-1` after
clean parse (2204/2454 files, zero module errors) — same family as the wrapper
receiver-proof `cannot establish invocation ledger` failures on 2026-10-11
runs 2-4. Nondeterministic shard-owner startup under multi-lane host load;
needs compiler-lane diagnosis of the shard owner startup/claim path.


## Phase 3 Table owner transfer, 2026-10-12

The actual frozen V7 full-CLI HIR pass reports four errors in async db_atomic
(group 92): the current SDN owner declares `Table(headers, rows)`, but the
consumer destructures obsolete `(fields, types, rows)` payloads.
The narrow async correction reuses upstream `af804c27f33b2104c30355323e78f5474e43b3ba`;
the same obsolete sync pattern is corrected separately. Required headers,
row order, scalar formatting, and existing non-table/missing-key errors remain.

Independent source review accepted both hunks and twelve production-helper
regressions. Those regressions remain AUTHORED_UNEXECUTED. Actual regenerated
HIR, MIR, object generation, native behavior, and whole Phase 3 tests are pending;
this transfer is not a bootstrap PASS. The live build uses its prior immutable
source and does not exercise these newly committed repairs.

## 2026-10-12 addendum 4: C7 — shard-path module-registry doubled-key + app-layer surface errors (full-CLI build)

Manual full-CLI build of the `src/app/cli/_CliMain/main_and_help.spl` closure
(2456 files, scv snapshot `scv-revision-v1-ac0b26f5`) failed HIR with 333
`module X has no exported item Y` lines across ~124 modules. Evidence log:
`/tmp/manual-cli-build2.log`; full 173-pair (module, item) inventory:
`/tmp/c7_pairs.txt` (regenerate: `grep 'has no exported item'
/tmp/manual-cli-build2.log | sed -E 's/.*module ([a-z0-9_.]+) has no exported
item ([A-Za-z0-9_]+).*/\1 \2/' | sort -u`).

**Root cause (compiler lane, NOT source):** the shard-path module surface
registry keys leaves by `module_logical_name_from_path`, which keeps the inner
directory segment of tier dirs that repeat their own name — leaves under
`src/compiler/70.backend/backend/` register as `compiler.backend.backend.*`
and under `15.blocks/blocks/` as `compiler.blocks.blocks.*` (doubled inner
segment), while the whole tree imports single-segment names
(`compiler.backend.native.mach_inst`, `compiler.blocks.builtin`). The
sequential path resolves both spellings via fallback, so only the
`--low-memory` HIR-shard path fails: module lookup is bridged to a surface
that does not carry the requested items. Corroborating evidence:

- The landed mach_inst wildcard fix (44e170a1c19,
  `export use compiler.backend.native.mach_inst.*` in
  `native/__init__.spl`) IS present in the failing snapshot, yet all 18
  mach_inst items still error — facade wildcarding does not clear this
  family.
- Failing items include `pub class`/`pub enum`/`trait` declarations in the
  very module named by the error (e.g. `compiler.backend.codegen_types`
  `CodegenOutput`/`CodegenOutputKind` at
  `70.backend/backend/codegen_types.spl:23,30`; `GpuCodegen`/`HardwareCodegen`
  traits) — no facade is even involved.
- Every failing importing module reports exactly the first 10 items of its
  first `use` list (regalloc, isel_*, encode_x86_64, formula.spl) — a
  per-module 10-error diagnostic cap hides the true volume; whole surfaces
  are empty, not partially enumerated.
- The `app.ui.*` failures all involve dot-named source directories
  (`src/app/ui.browser/`, `ui.render/`, `ui.tui/`, `ui.test_api/`) whose
  surface keys are likely sanitized differently (cf. the hyphen→`_` key
  sanitization note in `module_import_resolution.spl`); `common.string_builder`
  and `app.t32_cli.mod` fail with no naming anomaly at all.

**Fix direction:** the shard registry must key surfaces by the sequential
path's logical-name derivation (same fold for doubled tier-inner segments and
dotted directory names), and the per-module error cap should be lifted or
summarized for diagnostics. Do NOT chase this family with more facade
wildcard edits.

**Genuine source gaps fixed in the C7 commit (independent of the registry
bug; verified declared-elsewhere items never surfaced by their module):**
`codegen.spl` re-exports `CodegenTarget` from `backend/backend_types.spl`;
`hardware_codegen_types.spl` now `export use`s `VhdlProcessKind` from
`compiler.mir.mir_data` (was `use`-only); `elf_writer.spl` routes
`write_elf64`/`align_offset` via `export use` from `elf_writer_serialize.spl`
(bare `export` of undeclared names drops them from the shard index);
`blocks/builtin.spl` wildcard-re-exports `builtin_blocks_math/data/shell`;
`blocks/registry.spl` re-exports `init_blocks` from `blocks/mod.spl`;
`bidirectional_checking.spl` re-exports `TypeInferencer` from
`bidirectional_inferencer.spl`; `driver_core_types.spl` re-exports
`BackendCompileOptions` from `backend/backend_types.spl`;
`build_native.spl`/`build_native_pipeline.spl` import `compile_to_smf` from
`compiler.driver.driver_api_compile_single` (module `driver` never existed);
missing `std.math.{special,financial,distributions,statistics}` and
`std.math.bignum.{bignat,limb}` leaves added as `src/lib/math/*.spl`
re-export facades + `mod math.*` entries in `src/lib/math.spl` (C6
addendum-3 idiom; only modules with real importers; `std.math.math`/`bignum.fixed`
are comment-only, skipped). NOT fixed here: the `src/lib/compiler/mir_opt/*`
stub facades self-reference their own module name (duplicate module-name
collision with the `60.mir_opt` canonical files) — needs a compiler-lane
dedup decision.

## 2026-10-12 addendum 5: C7 naming fix LANDED (module_path_naming tier-inner-repeat fold + doubled-spelling migration)

Fix: `_module_path_naming_strip_numbered_dirs`
(`src/compiler/00.common/module_path_naming.spl`) now folds the redundant
inner repeat of `NN.name/name/...` tier dirs, so path-derived keys equal the
import spellings the resolver already maps onto that tree
(`src/compiler/70.backend/backend/native/mach_inst.spl` now derives
`compiler.backend.native.mach_inst`, was `compiler.backend.backend.native.*`;
same for `15.blocks/blocks/*`, `60.mir_opt/mir_opt/*`, `50.mir/mir/*`,
`35.semantics/semantics/*`, `85.mdsoc/mdsoc/*`, `99.loader/loader/*`).
Exemption: 17 verified tier-root twins (e.g. `70.backend/backend_types.spl`
vs `70.backend/backend/backend_types.spl`, both `__init__.spl` pairs) keep
their doubled inner name — the resolver probes the tier root first, so the
tier-root file owns the collapsed spelling and collapsing the inner twin too
would give two physical files one registry key. Tree-wide migration: 639
`.spl` files rewritten from doubled to single import spellings (exempt twins
and module-only `compiler.X.X.{...}` imports untouched); dotted dirs
(`ui.browser`) verified unaffected (sanitizer already preserves `.`).

Validation (admitted stage2 compiler
`.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple`,
with SDKROOT/MACOSX_DEPLOYMENT_TARGET from `xcrun --sdk macosx`):

- A. Sequential control: `native-build --source src/compiler --source src/lib
  --entry src/compiler/bootstrap_admission/stage2_module_path_naming.spl
  --runtime-bundle core-c-bootstrap --runtime-path
  phase2-runtime-capsules/75f976a0…` — PASS (exit 0, artifact published,
  binary prints the fixture's three expected module names). `--source
  plugins` and out-of-tree entries are rejected by SCV admission
  (`source-inventory-scope-unsupported`); the smf_package phase prints a
  non-fatal `state=failure` line even on success.
- A2. mach_inst-as-entry control (sequential): 0 import errors; fails at MIR
  with 25x "cannot derive module static type from unresolved initializer"
  (mach_inst.spl:196 module statics) — byte-identical failure at pristine
  HEAD, pre-existing, unrelated to this change.
- B. Doubled-dir shard repro (`native_elf.spl` entry, `--low-memory
  --threads 2`, default roots): still fails with the C7 signature
  (47 "has no exported item" + 4 "missing module surface", modules keyed
  doubled, e.g. `module=compiler.blocks.blocks.mod`) — EXPECTED: the
  admitted binary is PREBUILT with the old derivation, so it cannot exhibit
  the fix. The fix only takes effect in a compiler built FROM these sources
  (normal stage-3 rebuild). Full end-to-end B must be re-run after the next
  bootstrap; the separate shard-index export-drop mechanism
  (`cold_hir_compiler_publication_v1.spl`) remains a suspect for residual
  failures and needs its own diagnosis if the family persists post-rebuild.
- Unit: a check binary built from the new `module_logical_name_from_path`
  printed all 15 probe paths exactly as designed (collapse for non-twins,
  doubled preserved for the 17 exempt twins, dotted dirs unchanged).
- Side fix: 5 pre-existing malformed/misplaced `@workaround` markers in
  cuda_backend.spl / auto_vectorize_validate.spl / isel_x86_64.spl
  (missing `reason=`, or separated from their block by comments) failed
  workaround refresh once the files were touched by the migration; repaired
  in this commit.

## 2026-10-12 addendum 6: stage-2 gate residual three (db_atomic arity, B5b cascade, aspect_pack_io types)

- db_atomic.spl: `case SdnValue.Table(fields, types, rows):` (3 slots) vs the
  sibling-changed declaration `Table(headers: [text], rows: [[SdnValue]])`
  (2 payloads, src/lib/common/sdn/value.spl:36). Fixed to
  `case SdnValue.Table(headers, rows):` with `columns = headers` (the
  Option<fields> column-header handling died with the third payload; the
  sibling change made headers required). Seed validation blocked by a
  pre-existing gc-boundary policy artifact in standalone mode
  (nogc_async_mut -> std.nogc_sync_mut.io.time_ops); arity fix verified by
  inspection against the declaration.
- B5b ("match has multiple wildcard arms", test_runner_build): the only
  module named by the error batch is lib.common.sdn.value
  (`undefined variable SdnValue` + `unresolved method call: Float` both at
  value.spl:48:9 — the enum's own constructor fails inside its impl, i.e.
  the enum's symbol IDENTITY was clobbered earlier in the 252-module MIR
  batch; the B5b check at 50.mir/_MirLoweringExpr/expr_dispatch.spl:6466
  then fires on a FlatAst-bridge-degraded wildcard arm per the documented
  mechanism, convert_nodes.spl:1581/1628-1631). value.spl compiles CLEAN
  standalone (seed semantics + SMF) and contains no match with two wildcard
  arms (all 20+ matches inspected; every `case _` is single). No source fix
  is applicable. Compiler-lane hardening proposed: (1) always-eprint a
  receipt (file:line + expression tag) when convert_flat_pattern degrades a
  pattern to Wildcard — currently behind SIMPLE_DEBUG_MATCH_PAT, default
  off; (2) include the lowering module name in the B5b diagnostic.
- aspect_pack_io.spl: 10x `unresolved type: MappingClosePermitV1/
  MappingLifetimeLedgerV1/MappingLifetimeRecordV1` (fix-(b) class; owner
  exec_mapping_cleanup_v1 itemizes the imports but the shard-path
  owner-scope sweep cannot see them). Cheapest source-side unblock applied:
  explicit itemized import of all three types added to the IMPORTER
  (aspect_pack_io.spl) from their declaring module
  compiler.loader.mapping_lifetime_accounting_v1 — local binding dodges the
  owner-scope projection the same way the fe1f4ed6d72 workaround imports
  do. Seed standalone validation blocked by the same sffi_env_get stdlib
  gap as before; confirmation requires the matrix rerun. If the matrix
  still reports these after the importer-side import, compiler fix (b)
  (alias-retry in canonical_callable_dependency_candidate) is unavoidable.

## 2026-10-12 addendum 7: aspect_pack_io revert + fix (b) landed + B5b minimal repro and confirmed mechanism

- REVERTED the aspect_pack_io.spl importer-side import (af804c27f33 hunk): in
  the newest matrix it converted the transitive miss into a hard "module
  compiler.loader.mapping_lifetime_accounting_v1 has no exported item
  MappingClosePermitV1" — the structs ARE exported (mapping_lifetime_accounting_
  v1.spl:518-519), so the shard-path SURFACE PUBLICATION drops them; importing
  them names the drop as a hard error (54 hir-fatal). Strictly worse than the
  original 10 transitive errors; reverted.
- Fix (b) LANDED (module_reexport_materialization.spl,
  materialize_imported_callable_explicit_dependency_inner): when a frozen
  import row's import_target_indices[i] is -1, retry the target via
  module_surface_resolve_absolute_key + module_surface_registry_index against
  the frozen registry before declaring the route missing. The retry is a pure
  function of the frozen registry (generation fixed per lowering run), so the
  RISFACT memo invariant is preserved. Validation: seed semantics identical to
  pristine (only the pre-existing sffi_env_get standalone artifact);
  stage2_module_path_naming fixture native-build PASS (exit 0, artifact
  published, expected fixture output). Full validation = next matrix run.
- B5b CONFIRMED MECHANISM (decisive minimal repro, writable tree):
  `native-build src/lib/common/sdn/parser.spl --emit-object --backend=llvm
  --threads 1` (admitted compiler, fresh HOME) reproduces "B5b: match has
  multiple wildcard arms" with a 3-module closure (parser + sdn.value +
  structural_scalar_value_v1). sdn.value ALONE and structural_scalar ALONE
  compile clean (exit 0, object emitted). db_atomic-as-entry (50-module
  closure) reproduces B5b + 2x "unsupported Result tuple payload element
  type". Live-edit marker confirmed the build reads live source.
  Mechanism (proven by exhaustion): in the streaming/shard MIR path the
  SdnValue and Result ENUM TYPE REGISTRY ENTRIES are not visible while an
  IMPORTING module lowers (value.spl's own statics fail identically in larger
  closures: "undefined variable SdnValue at value.spl:48:9", "unresolved
  method call: Float"). Every enum pattern over an unregistered enum degrades
  to a wildcard/binding arm; a two-arm Ok/Err match degrades to TWO wildcards
  (B5b, expr_dispatch.spl:6466), and a single-arm match degrades to a
  wildcard PLUS the compiler's synthesized exhaustiveness fallback — also
  B5b. Converting parser.spl's matches to `if val Ok/Err` form (the rt_hal
  idiom) does NOT help: `if val` lowers to the same match. Any type position
  naming the unregistered enum degrades too (v.as_dict() loses Dict typing ->
  "unresolved method call: keys"). CONCLUSION: not source-fixable module by
  module; COMPILER-LANE root = enum type registration missing at MIR lowering
  time for imported enums in the streaming shard path (HIR registers them —
  HIR phase passes; the MIR-side flat/global symbol handoff drops them).
  RECOMMENDED COMPILER FIX (recorded, not guessed): in 50.mir
  _MirLowering/bootstrap_globals, the cross-module symbol accumulator must
  resolve enum type/constructor symbols through the HIR symbol table's
  owner-qualified binding (lookup_qualified_type_raw(owner, name)) instead of
  the flat short-name registry when the short-name entry names a different
  owner; plus the B5b diagnostic at expr_dispatch.spl:6466 should carry
  self.current_module_id (the binding-twin at :6506 already does). Hardening
  also recommended: always-on receipt when a match arm's enum pattern has no
  registry entry (currently silent degradation).

### Addendum 7 implementation status (c556a66e4fd follow-up)

IMPLEMENTED the recorded B5b compiler fix (pending next admission for
functional validation — the admitted binary predates the fix, so the fast
repro cannot flip green until the next stage-2 build):
1. expr_dispatch.spl NamedVar arm: owner-qualified retry — when the flat
   short-name resolution yields a symbol id that is neither a local nor a
   registered global read, and the symbol's defining_module differs from
   self.current_module_id, retry via symbols.lookup_qualified_type_raw(owner,
   name) before the "undefined variable" error. Declaring-module registration
   is authoritative over importer pre-registrations.
2. expr_dispatch.spl B5b diagnostic now carries self.current_module_id (the
   binding twin at the :6506-class message already did).
3. convert_nodes.spl: the match-pattern degradation receipt
   ([match-pat] convert_flat_pattern DROPPED to wildcard: tag=N) is now
   ALWAYS ON (was gated behind SIMPLE_DEBUG_MATCH_PAT), so a degraded arm is
   attributable at parse time instead of surfacing as a location-blind B5b
   much later.

Controls run with the OLD admitted binary (expected: repro unchanged until
admission): parser.spl repro exit 1 with B5b (repro intact); sdn/value.spl
alone exit 0; stage2_module_path_naming fixture exit 0 with correct output;
db_atomic 50-module closure still shows B5b + 3x "unsupported Result tuple
payload element type" (the Result-tuple-payload family is tracked separately
and may need the same owner-qualified treatment in the enum-payload
materialization path on the next iteration). Seed semantics of all changed
files identical to pristine (only the pre-existing sffi_env_get standalone
artifact). Functional validation: next matrix/admission run.
- Novel cause (2026-10-12, stage-2 seed regression from 4bec5687ee6): the new
  declaration_{providers,default_bindings,default_rewrite}_v1.spl referenced
  `HirConst` through a bare `use compiler.hir.hir_definitions.*` glob, but
  HirConst is neither pub nor exported there — the glob does not provide it
  under the Rust seed (self-hosted directory-package visibility masked this),
  so `HirConst(...)` literals in
  register_provider_global_bindings_with_initializer_policy_v1's callees
  resolved to struct ANY and seed HIR failed with "cannot infer field type
  ... struct 'ANY' field 'type_'". Fix: explicit itemized
  `use compiler.hir.hir_definitions.{HirConst}` in all three files (every
  other 50.mir consumer already imports it itemized). Also fixed a latent
  `field.type_` (undefined in scope; now `field_type`) in the extracted
  register_composite_field_metadata_types_v1.

Canonical Windows attempt13 independently reached this extracted function on
frozen source `5c891cd74242833f3dee8a88da264a73a242fae1`: the Rust seed compiled
1,297 files and failed one, `50.mir/_MirLowering/module_lowering.spl`, with
`cannot infer field type while lowering MirLowering.register_composite_field_metadata_types_v1:
struct 'ANY' field 'type_'`. All four support builds finished. The native build
terminated with exit1, quiescent1 and measured peak1,251,560 KiB under the
5,859,375 KiB enforced process-tree cap (jobs3). No new compiler was admitted;
fresh Hello, CLI and runner checks were not run. Original logs and hashes are
retained in `C:/dev/simple-phase3-bootstrap-evidence/attempt13/final-summary.env`.
Latest release `a95346aaef7a04c2e0935b2816e6157dd497457d` includes the typed
`field_type` correction. Its actual rebuild/admission remains pending.
- Novel cause (2026-10-12, candidate_frontend_smoke p2_add admission):
  runtime_tagged_callback_owner_v1.spl nm-parsed required core-C symbols with
  EXACT name matching, but Mach-O nm always prepends a leading underscore to C
  symbols (`_rt_tagged_add`), so no required symbol ever matched on Darwin and
  the gate failed with 'lacks defined function
  rt_transient_array_scope_state_v1' even though nm listed it as defined text
  (added 54908626175). The gate (e98757b4d8e) passed Linux CI (no underscore)
  and failed on its first macOS run. Fix: strip a leading underscore from the
  parsed symbol name (matches both ELF/GNU and Mach-O spellings).

### Addendum 7 follow-up (155dc9eb lane): sffi/plugins import fixes + constructor-path retry + executor ambiguity recorded

- runtime.spl: `type RuntimeValuePtr = i64` declared at the point of use —
  the alias existed only in compiler/70.backend/sffi_minimal.spl, so all 24
  extern signatures in sffi/runtime.spl failed with 'unresolved type:
  RuntimeValuePtr' and poisoned every sibling projection. Seed-validated:
  runtime.spl now compiles standalone.
- exec_mapping.spl: `export exec_mapping_map_rx, exec_mapping_free` added —
  both object_mapper files (loader/object_mapper.spl:6 relative,
  99.loader/object_mapper.spl:5 absolute, both resolving to this module under
  the collapsed naming) imported items the module never exported (HirConst-
  class visibility bug).
- B5b constructor-path extension: static_enum_receiver_owner.spl
  (try_lower_declared_enum_static_call) now applies the same owner-qualified
  retry as the NamedVar arm — when the flat lexical lookup misses and the HIR
  node's symbol names a foreign defining_module, retry via
  lookup_qualified_type_raw(owner, name). `SdnValue.Float(f)` is a
  named-constructor MethodCall (this path), not a NamedVar. Pending
  validation: next admission (3-module parser.spl repro must flip green).
- executor.spl:65 'Optional record has ambiguous current provider
  declaration' (test_runner_build): the text? Some-record's layout identity
  matches TWO Struct/Class symbols in the lowering symbol table
  (optional_record_owner.spl:64-68). Registry-level duplicate-declaration
  family; every Some-destructuring of that Option in the module hits it, and
  `.?`/if val lower through the same machinery, so no safe source workaround
  exists. Recorded for the compiler lane: the ambiguity diagnostic should
  name both colliding declarations (symbol ids + owners), and the
  duplicate-struct dedup should consider Option-record provider layouts.
- Stage-2 self-build pair (2026-10-12, regression from 43c3f3d979a): (1)
  archive_borrowed_module_v1.spl — 'struct ANY field symbol' in
  lower_archive_module_in_owned_scope_v1: MirHirDeclarationRepositoryV1 /
  MirHirModuleDeclarationsV1 came only through the summary module's nested
  'export use ... .*' re-export glob, which the seed registry does not
  materialize one level up; explicit itemized import from
  hir_declaration_types_v1 added. (2) driver_pipeline_lowering.spl —
  'Aliasing violation: reference 9 already has Exclusive' in the new
  publish_runtime_std_mir_emissions_v1: 'val selection = self.ctx....!' held
  an Exclusive borrow on self.ctx across the source loop while
  self.ctx.add_error re-acquired Exclusive inside it. Fix: never bind the
  unwrapped aggregate — hoist its two used scalars via inline '.?.field'
  chains before the loop (the pattern cold_full_index_producer_v1.spl:139-140
  already uses and the seed accepts).
- Closure-verified corrections (2026-10-12, supersedes the masked standalone
  diagnoses): (1) archive_borrowed_module_v1.spl — the itemized
  MirHirDeclarationRepositoryV1/MirHirModuleDeclarationsV1 import IS
  closure-effective (0 'cannot infer field type' in the entry-closure build);
  the prior 'persists' report was the stale-snapshot bulk build. Root cause
  remains: hir_declaration_types_v1.spl exports NOTHING and the summary
  module's 'export use ... .*' re-export does not materialize under the seed.
  (2) driver_pipeline_lowering.spl — true root: 'for source in
  self.ctx.sources' holds an Exclusive borrow on self.ctx (reference 9) for
  the whole loop, so EVERY inner self.ctx access (read probes and
  self.ctx.add_error alike) re-acquired it. Scalar hoisting of the selection
  alone could not cure that. Fix: snapshot ALL six self.ctx fields the loop
  touches into locals BEFORE the loop (sources, cold_hir_typed_receipts,
  mir_modules, runtime_std_cfg_decisions, native_target,
  runtime_std_hir_emissions); no self.ctx borrow is live inside the loop, so
  add_error's Exclusive acquisition is uncontended. Closure-verified: 0
  'Capability error/Aliasing' lines. Both verified with admitted binary
  cd1601c9 (sha matches admission.env) via entry-closure builds; the residual
  failures in those runs are the old binary's builtin-class receipts
  (Option/Result/Dict, fixed in fe1f4ed6d72) and shard-inventory
  infrastructure, not these files.
- Full-closure-safe restructures (2026-10-12, on top of a791b5e5cd1): the
  single-file entry-closure passes were necessary but not sufficient — the
  interference is bulk-context registry/borrow state. (1)
  archive_borrowed_module_v1.spl: every registry-projection element is now
  bound to an explicitly annotated local before any field read — 'val
  primary: MirHirModuleDeclarationsV1 = ...', and the nested globals loops
  rewritten to index-based iteration with 'val global/own_global:
  MirHirGlobalDeclarationV1 = ...[i]' (for-in element types degrade to ANY
  in the bulk closure; the annotation pins the real type).
  MirHirGlobalDeclarationV1 added to the itemized import. (2)
  driver_pipeline_lowering.spl: the source loop is now index-based
  ('while source_idx < sources.len(): val source = sources[source_idx]'),
  keeping the six field snapshots — the for-iterator itself held the
  Exclusive borrow (reference 9) across the body. (3) Preventive scan of the
  43c3f3d979a/4bec5687ee6 sibling files: declaration_default_bindings_v1
  already annotates its element bindings; declaration_default_rewrite_v1
  iterates only local collections; mir_lowering_types.spl:914 iterates a
  self field but never touches self inside the loop — all safe, no changes.
  Entry-closure validation (admitted cd1601c9, snapshots c24e5dd2 / file-2
  snapshot contain the restructures): 0 'cannot infer field type' and 0
  'Capability error/Aliasing' lines respectively. Real confirmation: next
  bulk build.
- Plateau bisection outcome (2026-10-12): with 1540f5def5f in the tree, the
  EXACT plateau command shape (dynload mode, full -o, --source
  compositions/kernel_llvm_cranelift + src + compiler + app + lib, admitted
  binary cd1601c9 + matching capsule) compiles BOTH former-failing files
  cleanly at full --source src scale: archive_borrowed_module_v1.spl and
  driver_pipeline_lowering.spl each appear in the HIR progress with ZERO
  'cannot infer field type' / ZERO 'Capability error' lines (verified in
  /tmp/bisect2.log, snapshot b28cbc59). The plateau log quoted to the lane
  predates 1540f5def5f. No interfering dir to isolate: the bulk-context
  registry/borrow interference is neutralized by the restructures themselves
  (annotations pin element types regardless of projection degradation;
  index-based loops hold no iterator borrow). The residual 93 hir-fatals in
  that validation run are the admitted binary's OWN pre-fix state
  (unresolved type: MirType/ImplBlock/LocalId/Option/Result/Dict — the
  builtin-guard and enum-retry fixes fe1f4ed6d72 / 20694e21a1a landed after
  cd1601c9 was admitted) — they confirm at the next admission, not a new
  interference source.

## 2026-10-12 addendum 8: SEED-verified fixes for the two persistent stage-2 failures (repro tool was wrong all along)

Repro tool correction: the stage-2 bulk build is performed by the RUST SEED
(worktree src/compiler_rust/target/bootstrap/simple, 217MB llvm build with
SIMPLE_BOOTSTRAP=1), NOT the admitted binary. Prior "passing" validations
used the admitted binary. Second tool correction: the SCV snapshot tracks
COMMITTED state only — uncommitted edits never enter the seed build (the
revision id stayed fixed across working-tree changes); every fix below was
verified only after commit.

Seed repro command (all three now exit 0):
  env SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 \
  src/compiler_rust/target/bootstrap/simple native-build <file> --entry-closure \
  --source src/compiler --source src/lib --emit-object --backend=llvm --threads 2 \
  --cache-dir <fresh> -o <out>

1. archive_borrowed_module_v1.spl — "struct 'ANY' field 'symbol'": TRUE root
   was the `for selection in selections:` loop + `for raw_function in
   module.functions.values():` — the values()/for-in ELEMENT arrived as ANY
   from the seed's aggregate typing, and an annotation on an ANY-typed RHS is
   not authoritative ("seed aggregate typing not authoritative" warning).
   Fix (239e9e00575): index-based loops with explicitly annotated element
   locals. Supporting fixes that were necessary but not sufficient:
   export the MirHir carrier structs (5fe16d201c9); itemize the types in
   summary/codec/consumer/bindings/providers/artifact (d65deffb, 36de1602)
   because 'export use ... .*' neither imports into the declaring module's
   own scope nor propagates one glob level up under the seed.
   SEED-VERIFIED: exit=0, 0 'cannot infer field type'.
2. driver_pipeline_lowering.spl — "reference 9 already has Exclusive": TRUE
   root was the seed capability checker's acquire semantics: `&mut` is the
   ONLY acquisition site (hir/lower/expr/operators.rs), borrows are released
   ONLY at function end or the call-argument checkpoint, and that checkpoint
   applies ONLY to proven_nonescaping_functions (module_pass.rs:482 —
   requires an all-'pass' body, so real callees never qualify). Four call
   sites passed `&mut lowering` to callees whose params are by-value
   `mut lowering: MirLowering` — the `&mut` was redundant (Simple derefs)
   and the second acquisition on the same local id was the violation.
   Fix (73fd4189bdb): dropped the redundant `&mut` at all four call sites
   (driver_pipeline_lowering.spl x3, hir_mir_archive_consumer_v1.spl x1).
   Also (f4f37c5bec2): renamed the elif-arm measured_execution binding —
   defensive against the same never-release semantics across branches.
   SEED-VERIFIED: exit=0, 0 'Capability error'.
3. declaration_providers_v1.spl (earlier HirConst itemization):
   SEED-VERIFIED: exit=0, 0 'cannot infer field type', 0 HirConst mentions.
- Stage-3 E-MONO-032 batch (2026-10-13): 160 errors / 147 unique sites / 20
  callees — all annotated with explicit generic type arguments. walk_hir_* /
  walk_ast_* recursive sites got '<C>' (generator fold_gen.spl fixed to emit
  '<C>' so generated files don't regress; generated files patched to match).
  _sffi_* / _driver_vhdl_* / h_* / transient_heap_promote_v1 sites annotated
  with the argument's concrete enum/record type (MirInstKind, HirExprKind,
  HirTypeKind, MirTypeKind, HirUnaryOp, MirOperandKind, Result<...>,
  CompileSourceEventV1, BlockDefinition, i64/text keys). Ambiguous choices:
  _sffi_tuple_get over raw i64 encodings uses the PAYLOAD target type
  (LocalId/text); the local non-generic _sffi_tuple_get in
  llvm_lib_translate_expr.spl was renamed _sffi_tuple_get_i64 to dodge the
  generic twin in expr_dispatch.spl (co-compiled duplicate confusion).
  Seed standalone parity on all touched files (same artifact as pristine).
