# Stage-3 self-build MIR cluster 2026-11-14: re-export chase dead-ends + callable-return-type loss

- **Date:** 2026-11-14
- **Status:** chase dead-ends and the receiver-typing/bare-Ok classes FIXED (source-side, probe-verified); the section-D classes (non-exhaustive matches, I8 registration, ambiguous layouts, Nil-is-unit payload mismatch, adaptive_map for-in, llc i64-vs-ptr emission) remain and are the next layers
- **Area:** `src/compiler/20.hir` (re-export chase), `src/compiler/50.mir` (method-call/match lowering), compat facades under `src/app/io`, `src/lib/nogc_*`
- **Evidence:** gen4-lane `stage3-native-build.log` @ pinned 31381ce21fa (fatal_count=40, 70 mir_errors items in `app.cli.bootstrap_main`'s bootstrap_fixed lane); reduced-probe transcripts under `build/hir-probe/` in worktree perf-fix-hir2

## Symptom

Stage-3 self-build (stage2-admitted binary compiling the 1692-module
`bootstrap_main.spl` closure) fails MIR lowering with ~70 items in ~10 classes.
The two headline classes:

1. `unresolved method call: is_ok / is_err / unwrap_err / insert / len ...
   owner=` (EMPTY owner — the receiver's HIR type was never recorded).
2. `enum match: bare variant 'Ok' is ambiguous ...; subject ... has type known
   non-enum type` (the match subject's recorded type is a non-enum placeholder,
   not the declared `Result<...>`).

Preceding diagnostics: 12 distinct `[hir-reexport-chase-unresolved]` items —
the chase could not route `file_copy`, `file_read_bytes`, `BinaryReader`,
`BinaryWriter`, `dir_list`, `file_hash_sha256`, `file_modified_time`,
`file_mmap_read_text`, `SYM_ENUM`, `SYM_CLASS` through their facades.

## Root causes (per class)

### A. Re-export chase dead-ends (source-side, FIXED)

The chase diagnostic is accurate: each named facade "neither declares this
name nor routes it through a resolvable re-export". Per-site verdicts:

| facade | item | canonical owner | fix |
|---|---|---|---|
| `app.io.file_ops` | `file_copy` | `std.nogc_sync_mut.io_runtime` | importer-side: dropped from the `compile_targets.spl:15` import (already imported canonically at :92 per #9025) |
| `app.io.file_ops` | `file_read_bytes` | `std.nogc_sync_mut.io_runtime` | importer-side: `elf_artifact_gate.spl:12` now imports it from there |
| `lib.nogc_async_mut.binary_io` | `BinaryReader`, `BinaryWriter` | `std.common.binary_io` (declares `BinaryReader`/`BinaryWriter`/`BinaryBufferedReader`/`BinaryBufferedWriter`) | facade-side: the dedup left the type names out of the re-export list; added them back (`binary_io.spl`) |
| `lib.nogc_sync_mut.io_runtime` | `dir_list`, `file_hash_sha256` | `std.nogc_sync_mut.io.dir_ops` / `std.nogc_sync_mut.io.file_ops` | facade-side: the async facade re-exported names the sync module never declared; rerouted (`nogc_async_mut/io_runtime.spl`) |
| `lib.nogc_sync_mut.sffi.io` | `file_modified_time`, `file_mmap_read_text`, `dir_list` (+ unflagged `file_read`) | `io.file_ops` / `io.dir_ops` / `io_runtime` | facade-side: same stale-name class in `nogc_sync_mut/ffi/io.spl`; rerouted |
| `compiler.driver.shb.shb_reader` | `BinaryReader` | — (ShbReader's field type surface) | importer-side: explicit `use std.binary_io.{ByteOrder, BinaryReader}` in `cache_validator.spl` (the file's own documented 2026-08-06 pattern) |
| `compiler.frontend.core.types` | `SYM_ENUM`, `SYM_CLASS` | declared NOWHERE | facade-side: dropped from the `export` line (`types.spl:1917`), same as 335af16de21's `SYM_UNKNOWN` |

No compiler-side chase defect found: every dead-end was a stale or incomplete
facade re-export list, not an unhandled re-export form.

### B. Empty-owner method calls (receiver HIR type never recorded)

Micro-probes (stage-2 binary, `build/hir-probe/probe_trait*.spl`, probe7-29)
isolate the mechanism: **when a call expression has no computed type, the
caller's local loses its type AND its own type annotation is discarded with
it** (`receiver_has_type=false receiver_type_kind=-1`). Three callee shapes
produce an untyped call:

1. **Trait-object method call on a trait-typed parameter** (`probe3`
   unannotated FAILS; `probe18/20/21/22` annotated STILL FAILS — param
   traits, with/without impl, with/without call sites). A factory-returned
   trait with a no-arg method types fine (`probe4/5` PASS), but an
   args-taking method fails even there (`probe19` FAILS). Generic
   `<L: Trait>` bounds fail the same way (`probe24`).
   Fix that WORKS (probe25/29 PASS): route the call through an identity fn
   with a declared Result parameter — `fn as_r(r: Result<T, E>) -> Result<T, E>: r`
   — the typed parameter types the argument expression.
   -> `go_to_end_trial_link_v1.spl` (`go_to_end_trial_link_result_v1`).
2. **Untyped-param fn** (`probe7` FAILS, `probe8` PASS): a call to
   `fn write_varint(value) -> [i64]` leaves the local untyped (no callable
   type is built), so `encoded.len()` fails. Typing the param
   (`value: i64`) fixes every call site -> `serialization/__init__.spl:287`.
   Variant: generic static call whose type args are not inferable from the
   arguments (`val map = Map.with_capacity(...)` in `src/map.spl:482`,
   `insert` unresolved) — fixed by annotating `val map: Map<K, V>`.
3. **Mono-specialized generic-method call** (`probe12/13` FAIL; `probe13c`
   shows the local's annotation is discarded too). The typed-param identity
   ALSO beats this (`probe27` PASS — the wrapper types the expression even
   when the callee is specialized). This is the rti004 family
   (`rti004_mono_specialization_match_subject_2026-11-01.md`) still live in
   the current stage2.
   -> `simple_ring.spl` (`_as_{reservation,token,unit}_result_v1` at the
   241/244/340/386 sites), `file_fiber_tldr_bridge_v1.spl`
   (`_as_ring_unit_result_v1` at both `self.ring.release` sites).

The compiler-side root to fix later: a `val x: T = init` binding must record
`T` on the local even when `init` has no computed type (today the annotation
is dropped), and trait-object / specialized-generic method calls must produce
their declared expression type. RTI path:
`src/compiler/20.hir/return_type_interface_v1.spl:718` (`callee_return`) —
`DynTrait` receivers are explicitly "RTI PR2" (unhandled).

### C. Bare-`Ok` ambiguity

The ambiguity is NOT a scope leak from the chase failures. It fires when the
match subject's recorded type is a non-enum placeholder ("known non-enum
type"), so no owner enum can be established; both bare AND `Result.`-qualified
arms then fail. All observed sites are class-B callees as match subjects:

- `backend_helpers.spl:590,600` (bare arms on imported-fn calls) — fixed
  with the typed-local + qualified-arms idiom (cleared in probe_min2).
- `backend_helpers.spl:611` (annotated local from the args-taking
  `Codegen.compile_module` trait call) — fixed with the typed-param identity
  `_as_codegen_compile_result_v1` (class B.1).
- `simple_ring.spl:241,244,340,386`, `file_fiber_tldr_bridge_v1.spl:348`
  (subjects are specialized-generic calls or locals annotated over them) —
  fixed with the typed-param identities (class B.3); the 241 payload binder
  additionally carries the file's provenance re-bind idiom.

### D. Other classes in the same cluster (NOT chase-related, NOT fixed here)

- ~30 `non-exhaustive enum match` items (MirTerminator missing Throw/Resume,
  HirStmtKind missing AsmAssert, OptimizationLevel missing Basic/Standard,
  MirConstValue missing FloatLexeme, EffectKind missing Unknown, etc.) —
  genuine stale match sites: the enums gained variants; the seed tolerated
  the fall-through, the self-hosted compiler rejects it. Each needs a
  `case _:` or new arms at the match site.
- `enum construction: unregistered enum 'I8'` x5 — registration-order
  family (`emitted_enum_id_depends_on_registration_order_2026-11-13.md`).
- `struct copy of ambiguous bare layout 'JoinPoint'/'ElfSymbol'` — genuine
  duplicate declarations with different field lists (JoinPoint:
  `10.frontend/core/aop.spl:162`, `35.semantics/join_point_model.spl:115`,
  `85.mdsoc/weaving/join_point.spl:7`; ElfSymbol: `70.backend/linker/
  elf_parser.spl:57`, `backend/native/elf_writer.spl:172`,
  `introspection/elf_symbols.spl:8`); copy sites need module-qualified
  provenance.
- `HirStmtKind.Let: payload type mismatch` x3 — the OPEN Nil-is-unit family
  (`stage3_enum_payload_type_mismatch_nil_unit_2026-11-13.md`).
- `for-in over non-array iterables ... adaptive_map` x11 — iterable mir type
  I64 placeholder in the generic map module; same type-loss family as B.3.
  NOTE: the `insert` error at `src/map.spl:482` was the same family and is
  FIXED (annotated `val map: Map<K, V>`); the adaptive_map for-in sites were
  not individually located/fixed.
- `unsupported provider default for MirBuilder.loop_view_capture_v1` —
  FIXED: `mir_data.spl:167` now passes `loop_view_capture_v1: None`
  explicitly.
- `MIR lowering produced no local for this expression` — no location in the
  log; unclassified.

## Verification

- Reduced probes (stage-2 binary, direct lane, `--entry-closure`):
  - probe1 (`build/hir-probe/probe_main.spl`, pre-fix): reproduces the chase
    traces (6 items) and all four mir-module-failures (go_to_end x5,
    backend_helpers x1, simple_ring x4, serialization x2).
  - probe_min (chase fixes only): 0 `hir-reexport-chase-unresolved` traces.
  - probe_min2 (+ serialization/map/mir_data fixes): serialization cleared;
    backend_helpers 590/600 cleared (error moved past them to 611).
  - probe_min3 (ALL fixes incl. the typed-param wrappers): **0 chase traces,
    0 mir-module-failures through the whole MIR phase** (832-module closure).
    The build's later native_compile phase fails only on the pre-existing,
    separately-documented llc `i64`-vs-`ptr` emission family (19 modules,
    incl. modules never touched here — e.g. `compiler.mir_opt.loop_opt`,
    `lib.common.process.observation_v1`), which is the next defect layer, not
    a regression from these fixes.
  - Micro-probes: probe3 (trait-param, unannotated) FAILS; probe18/20/21/22
    (trait-param, annotated, impl/call-site variations) FAIL — the
    annotation is discarded; probe4/5 (factory, no-arg) PASS; probe19
    (factory, args) FAILS; probe24 (generic bound) FAILS; probe25/29
    (typed-param wrapper, param-trait, args) PASS; probe7 (untyped param)
    FAILS; probe8 (typed param) PASS; probe12/13 (generic instantiation)
    FAIL; probe13c (annotation) FAILS; probe27 (typed-param wrapper over a
    specialized-generic call) PASSES; probe9/10/11/15/16/28 (non-instantiated
    generics, impl blocks, unit-Result returns, bare-arm self-call matches)
    PASS — the trigger is the callee shape (trait-param / specialized /
    untyped-param), not the match or the module.
- Full `bootstrap_main.spl` probe after the fix (stage-2 binary,
  `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 SIMPLE_BOOTSTRAP_STAGE3=1`,
  `--mode dynload`, same source roots as the gen4 lane, worktree sources):
  the bootstrap_fixed lane now fails with **fatal_count=14, down from 40**,
  and the accounting is exact: 40 - 26 (8 unresolved-method + 6 bare-Ok +
  1 provider-default + 11 for-in, all fixed here) = 14. ZERO errors remain
  from the chase, empty-owner-method, or bare-Ok classes, and the ~30
  non-exhaustive-match items from the stage-3 log are not in the fatal set.
  The 14 residuals: 5x `unregistered declaration ...mir_fold_binop`
  (registration-order/mangling family, note the DOUBLED module path
  `compiler.mir.mir_instruction_graph.compiler.mir.mir_instruction_graph.`),
  3x `JoinPoint` + 2x `ElfSymbol` ambiguous bare layouts (duplicate
  declarations), 3x `HirStmtKind.Let` payload mismatch (Nil-is-unit family),
  1x adaptive_map for-in (was 11). The for-in reduction suggests the
  `src/map.spl` annotation cleared the same untyped-iterable root in most of
  adaptive_map's loops.

## Residual risk / next

1. Compiler-side (the actual root of class B): a `val x: T = init` binding
   must record `T` even when `init` has no computed type (today the
   annotation is discarded), and trait-object / specialized-generic method
   calls must produce their declared expression type. Until then the
   typed-param identity workaround is required at every such call site; new
   code will keep hitting this. RTI path to start:
   `src/compiler/20.hir/return_type_interface_v1.spl:718` (`callee_return`;
   `DynTrait` receivers are explicitly "RTI PR2" — unhandled).
2. The ~30 non-exhaustive matches (class D) are the next big fatal block in
   the bootstrap lane; mechanical but broad (add `case _:` or the missing
   arms per site).
3. The llc `i64`-vs-`ptr` emission family now surfaces in native_compile for
   every module whose MIR newly lowers (19 in the probe closure) — a
   separate, already-documented stage-2 codegen defect that becomes the
   binding constraint once the MIR classes are green.
4. `simple check`-level validation of the touched facades against every name
   in their re-export lists (only importer-requested items are chase-checked).

## 2026-11-14 residual families follow-up (work/stage3-residual-families-20261114)

The 14 post-#9048 residuals were attacked per family. Status: family 3
(HirStmtKind.Let x3) FIXED and probe-verified (see
stage3_enum_payload_type_mismatch_nil_unit_2026-11-13.md, 2026-11-14
follow-up section); families 1, 2, 4 fixes landed (below); family 5 (llc
i64-vs-ptr) deferred with evidence.

### Family 2: JoinPoint / ElfSymbol ambiguous bare layouts — renamed duplicates

The `struct copy of ambiguous bare layout 'JoinPoint'/'ElfSymbol'` fatals
come from genuinely duplicate STRUCT declarations sharing one bare name
(different field lists), so the bare-name layout registry marks the name
conflicted and every bare-provenance struct copy dies closed
(mir_lowering_stmts.spl:745). Three `struct JoinPoint` declarations:
`10.frontend/core/aop.spl:162` (8-field flattened frontend AOP, kept
canonical — most importers and the keep-first registration winner),
`35.semantics/join_point_model.spl:115` (forward join points),
`85.mdsoc/weaving/join_point.spl:7` (MIR weaving). Three `struct
ElfSymbol` declarations: `70.backend/linker/elf_parser.spl:57` (parser,
kept canonical — exported to ~7 linker modules),
`70.backend/backend/native/elf_writer.spl:172` (writer),
`70.backend/introspection/elf_symbols.spl:8` (standalone reader). (A
fourth `enum JoinPoint` in `lib/nogc_sync_mut/src/aop.spl:18` is an enum —
different registry, not part of the layout conflict.)

Fix: renamed the two non-canonical structs per name —
`join_point_model.spl`'s -> `ForwardJoinPoint` (+ aspect_weave.spl,
aspect_validation.spl), `weaving/join_point.spl`'s -> `MirJoinPoint` (+
weaving/types.spl, 85.mdsoc/security.spl, weaving/__init__.spl),
`backend/native/elf_writer.spl`'s -> `ElfWriterSymbol` (+
elf_writer_serialize.spl, native_elf.spl, backend/native/__init__.spl),
`introspection/elf_symbols.spl`'s -> `ElfIntrospectSymbol` (module-local).
No glob imports of the renamed modules exist; no string-literal references
to the old names; no dangling `JoinPoint`/`ElfSymbol` references remain
(grepped). With distinct names the bare-name conflict mark disappears and
bare-provenance copies resolve unambiguously.

Verification: introspection/elf_symbols.spl closure compiles clean through
MIR+codegen (only the expected no-main link failure); full bootstrap_main
probe below.

### Family 4: adaptive_map for-in — typed-param identity wrappers (free fns)

The residual `for-in ... adaptive_map.spl:221:29` is class B.3
(mono-specialized generic-method call carries no computed type; the for-in
subject's MIR type is the I64 placeholder). A bootstrap-lane fixture
(fake app.cli.bootstrap_main whose closure pulls
lib.nogc_sync_mut.src.collections.adaptive_map) reproduces the class
STRONGLY: 11 distinct for-in sites fail (storage_entries' hash arm at
:221, plus storage_entries() call sites at :237/:248, :274/:278, :425,
:454, :476, :608, :624, :631 in the pre-fix file) — f4-boot-before.log,
fatal_count=22. NOTE: the full 1692-module closure only ever showed :221
("was 11 -> 1" after the src/map.spl:482 annotation); the small closure
shows the map.spl annotation does NOT clear the other 10, i.e. that
clearing is closure-scale-dependent and fragile — all 11 sites got the
fix.

Fix shape matters: a wrapper METHOD on the generic struct is itself a
mono-specialized generic-method call and loses the type identically
(measured: f4-boot-after.log still fatal_count=22 with the method
wrapper). The wrappers must be FREE fns (the simple_ring.spl
`_as_*_result_v1` shape): `as_entry_pairs_v1<K, V>(pairs: [(K, V)])` and
`as_entries_v1<K, V>(entries: [OrderedMapEntry<K, V>])` at adaptive_map.spl
file scope; all 8 affected for-in subjects now bind through them.

### Family 5: llc `i64`-vs-`ptr` emission — DEFERRED with evidence (next binding constraint)

Not a small fix: an emission-family defect where an i64-typed local
reaches an LLVM ptr-typed slot (or the local was emitted with an erased
i64 type where the instruction needs ptr). Every occurrence is llc
rejecting a generated `module.ll`:
`error: '%lN' defined with type 'i64' but expected 'ptr'`.

Fresh evidence (this lane): the isolated 169-module adaptive_map fixture
closure (build/resid-probe/f4-boot-after2.log) reached native_compile
after the MIR fixes and failed 12 modules on exactly this signature —
lib.common.binary_io, lib.common.crypto.sha256,
lib.common.encoding.external_text, lib.common.process.observation_v1,
lib.nogc_async_mut... (facade duplicates std.*) — including
lib.nogc_sync_mut.src.collections.adaptive_text_set, a module this lane
never touched. Matches the #9048-era observation (19 modules in the
832-module probe closure, incl. compiler.mir_opt.loop_opt and
lib.common.process.observation_v1). The defect is in the stage-2 MIR->LLVM
emission (a local's MIR type is i64/erased where the consuming
instruction is ptr-typed); finding it needs an llc-failing module.ll
inspection pass (the AOT cache dirs are cleaned after each run — capture
module.ll from a live cache on the next run). Recommended next step: run
any llc-failing single-module compile with the cache preserved, read the
failing module.ll around the reported line, and trace the local back to
its MIR producer (likely an erased/placeholder MirType on a call result
or alloca).

### Family 1: `unregistered declaration '<doubled path>mir_fold_binop'` — foreign SymbolIds in shared struct-default rows

The 5x `enum construction: unregistered declaration
'compiler.mir.mir_instruction_graph.compiler.mir.mir_instruction_graph.mir_fold_binop'
at src/compiler/50.mir/mir_instruction_support.spl:260:34` residuals are the
`MirOperand.call_origin` struct-field DEFAULT (`= MirCallOrigin.Source`,
:260) materializing at omitted-field fills. Mechanism (from the
registration-side reading; the stage-2 binary cannot be instrumented and
the synthetic 64-cell id-alignment fixture sweep did NOT reproduce — the
failure needs the full-closure topology):

- The default expr stored in `struct_field_default_expr` carries the
  REGISTERING module's SymbolIds (per-module numbering restarts at zero).
- A consumer whose bare-name row was written by the declaring module (or
  the up-front composite inventory) lowers that expr against its OWN
  symbol table; the foreign id aliases whatever symbol shares the number
  — here the consumer's dotted-renamed `mir_fold_binop` import
  (`qualify_imported_function_symbol`, module_import_resolution.spl:149,
  renames imported fns to `<module>.<name>` under bootstrap closure).
- `enum_qualified_key` then prepends the owner module to the
  already-qualified name, producing the DOUBLED path, which misses the
  qualified registry -> fatal. (`enum_qualified_key`'s doubling is
  cosmetic here; the semantic defect is reading a raw foreign row.)
- The provider pass (`register_provider_struct`,
  provider_metadata.spl:861) already RELOCATES provider defaults into
  the consumer's table (the llvmglobals_2026-10-25 fix) and writes them
  under the module-QUALIFIED layout key unconditionally — but the
  omitted-field fill in `lower_struct_construct` read only
  `struct_value_layout_key(declaration)`, which is the BARE name whenever
  the consumer's imported struct symbol carries no defining module, so
  the relocated row was never consulted.

Fix (switch_operators_calls.spl, lower_struct_construct omitted-field
fill): when `struct_name` is bare, resolve the default row through the
declaration's module-qualified layout key(s) from
`struct_identity_layout_key` (the provider pass's relocated row),
accepting a qualified row only when its field list matches the
construction's (a same-named different struct can never donate its
defaults); fall back to the bare row otherwise. While-loop iteration
(for-in over Dict keys is broken in compiled native code,
module_lowering.spl:3357). Verification: full bootstrap_main probe (see
final section); the gen5 real lane showed 0x mir_fold_binop on its
instance (registration-order dependent), so this fix also covers the
probe-lane shape that produced the 14-residual inventory.

### Family 6 (new scope): `enum construction: unregistered enum 'I8'` x5 distinct sites

Present in BOTH the gen4 (pre-#9048, index 28-32) and gen5 (post-#9048,
index 17-21) real-lane logs — deterministic, lane-independent of the
#9048 fixes. Non-fatal (`self.error`, switch_operators_calls.spl:6099):
the construction's EnumLit type resolves to a Named symbol spelled `I8`
with no defining module, so neither the qualified nor the bare registry
has it. `I8` is a unit variant of SIX+ enums (MirTypeKind, PrimitiveType,
DType, tensor/weight-utils/types-util enums) and HIR registers every
variant as an `EnumVariant` symbol NAMED AFTER THE VARIANT with
defining_module=nil (declaration_lowering.spl:929 — the same
mono_tuple_get_nominal_owner_e_mono_041_2026_10_19 hazard the comment
describes: a Named type landing on an EnumVariant symbol has no proven
owner). The direct lane compiles `MirType(kind: MirTypeKind.I8)` and
nested Ptr(I8) fine (f6-direct probe, exit 0); the failure is
bootstrap-lane specific. Root-cause probe transcripts and the fix:
PENDING (see final section).
