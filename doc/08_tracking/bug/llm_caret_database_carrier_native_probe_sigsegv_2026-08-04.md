# LLM Caret database carrier native probe SIGSEGV

Date: 2026-08-04
Status: Resolved — compiler call-target fix and native crash guards verified 2026-08-09

## Exact reproduction

The admitted Phase 3 compiler
`baf30b4f054f044b4b25c49b1b51c11fa39b6530cfa6bf29deb41b1e6483f8ea`
built `src/app/llm_caret/messaging/database_worker.spl` with the explicit
`core-c-bootstrap` runtime bundle. After direct-import corrections in
`nogc_async_mut/env/paths.spl`, the third and final build completed 94 units
with zero failures and emitted a 223,632-byte binary, SHA-256
`c0350a3bac28ead949465404051c7735cd6428d3c1b2ab775944638603ca5998`.

The first real probe against a fresh database exits 139 before JSON. The binary
was quarantined at
`build/llm-caret-stage3-carriers/llm_caret_messaging_db.failed`; the canonical
path is absent and no provenance or carrier PASS is claimed.

## Localization

The unstripped adjacent fixture
`test/fixtures/app/llm_caret/pure_database_native_probe.spl` proves:

- `PureDatabase.memory()` and `PureDatabase.close()` complete;
- `PureSqlMessagingStore.open_memory()` completes schema initialization;
- `PureSqlMessagingStore.ready()` enters the store-local
  `integer(DbRow, i64)` helper with a null `DbRow` (`rdi = 0`) and faults.

GDB resolves
`pure_sql_store.integer -> PureSqlMessagingStore.ready -> spl_main`. This
points to native `[DbRow]` element/argument lowering rather than database
open/close. Fix the compiler lowering owner and publish a newly admitted
compiler before rebuilding. Do not restore the canonical artifact until the
real probe exits zero.

## Fresh Stage 3 confirmation

Sanity-passing Stage 3 SHA-256
`1a94c1af1a91344b32bcedacda473fac40dfef6f32e254e5b38f10e4710452b0`
builds the current database worker in 95 units, but reports nine unresolved
stub fallbacks. The isolated artifact then exits 139 on its first fresh
database probe before JSON, matching the prior native failure. No provenance
was written and the other four shared-store carriers were not rebuilt.

## Imported receiver inference continuation

The retained Phase 3 capsule compiled the focused flat imported-method spec
three times with `SIMPLE_NO_STUB_FALLBACK=1`; no full bootstrap or messaging
carrier build ran. The first cycle disproved `SymbolId` value-argument removal
as sufficient. The second exposed a valid parameter symbol but an Option
carrier where its named `HirType` was expected. The third bare-lifted inferred
types and used the established nil-check/`??` extraction idiom. Receiver
diagnostics then advanced from `unknown` to concrete `Shared`, while HIR
lowering remained clean (`lower=0`).

The remaining instance lookup still reports no method for `Shared` even though
the exact index contains `owner_a.Shared::cleanup`; the indexed `Cell.to_text`
receiver is still unknown. `SymbolTable.lookup_method_in_type` and its
`method_symbol_name` helper both accept value-type `SymbolId`, the same staged
native ABI shape already avoided by `get_symbol_raw`. The next continuation
must convert that lookup boundary to raw `i64`, retain canonical owner names,
and rerun only the focused regression before rebuilding the Phase 3 capsule.

## Raw method lookup continuation

Three more strict retained-cache cycles converted instance, static, and trait
method naming/lookups to raw symbol IDs while preserving compatibility wrappers.
The focused matrix improved from seven resolver errors to three: parameter A/B,
static A/B, the direct constructor, and the trait-default call now resolve to
their exact canonical owners.

Both imported factory calls still expose the identical corrupt return type ID
`103079215111`, so their computed method key collapses to bare `cleanup`; changing
the imported callable optional return to bare lifting did not alter that value.
The nested `Row.values[0]` receiver also remains unknown after raw-ID field-owner
lookup. This localizes the next continuation before semantic resolution: inspect
the retained `ModuleSurfaceCallable` function-return payload and
`ModuleSurfaceField` container-element payload at construction and immediately
after surface transfer. Do not rebuild the Phase 3 capsule or any messaging
carrier until both IDs are valid in the focused matrix.

## Imported surface repair and remaining enum payload blocker

Native-safe scalar projections on module-surface callables, parameters, and
fields now preserve imported factory return and array-element type names. Raw
qualified-type and named-type lookups avoid the staged-native optional/value
ABI boundary. The focused exact/adjacent imported-method regression passes
1/1, including parameter, constructor, factory, static, trait-default, indexed
field, and imported-enum method owner resolution.

A strict retained-cache Phase 3 rebuild completed with 4 compiled, 721 cached,
and 0 failed. The database-shaped fixture
`test/fixtures/compiler/native_imported_struct_array_argument_probe.spl` now
builds without stub fallback and no longer SIGSEGVs. It exits 2 because
`DbValue.Text(value: "1").to_text()` returns `<enum@...>` instead of `"1"`.
The adjacent local-enum fixture passes, proving ordinary native enum text
payload decode works when construction and match share a lowering unit.

Three bounded cycles attempted to carry text payload truth from the binding
semantic type and from tuple/named-field enum declarations. The imported
fixture remained identically red, which indicates that metadata still does not
reach the lowering instance that emits the imported `DbValue.to_text` body.
The ineffective MIR candidates were removed after the third red cycle; the
diagnostic fixtures and the earlier green surface/raw-ID repairs remain.
Do not rerun the unchanged fixture or rebuild the database carrier. The next
owner must trace module/impl body MIR lowering state transfer for
`enum_payload_struct_names`, then add a source-level regression proving the
declared `DbValue.Text` marker is present in that exact lowering instance.

## Direct imported enum emission localization

The smaller fixture
`test/fixtures/compiler/native_imported_enum_text_payload_probe.spl` removes
`DbRow`, arrays, field projection, and PureDatabase. A strict retained Phase 3
build succeeds with three compiled modules and zero stub fallback, but the
direct `DbValue.Text(value: "direct").to_text()` result is still `<enum@...>`.
The equivalent local enum fixture passes. Therefore the remaining defect is
not array/row transport and precedes the database carrier.

A focused registry regression proved that declaration metadata survives
copy-modify-reassign under bare, runtime-qualified, and raw-symbol keys. Three
bounded capsule cycles then tested native-safe dictionary reads, qualified/raw
symbol lookup identity, and a gated `Text`-arm lowering receipt. The executable
remained identically red, while per-module worker stdout hid the receipt. Those
ineffective MIR candidates and the temporary print were removed; the final
diagnostic capsule is intentionally not source-matched or admitted.

The next continuation must produce durable flat-MIR evidence rather than
another runtime guess: persist or expose the emitted function name/body and
the consumer call operand for `DbValue.to_text`, then assert they identify the
same canonical symbol and that the emitted body contains `rt_enum_payload` plus
the text decode. Do not rerun either imported enum fixture unchanged until that
source-level/emission evidence identifies a concrete mismatch.

## Retained-object call-target evidence and bounded Rust audit

Forcing only the final link to fail retained the three LLVM objects. The
provider object defines the canonical imported `DbValue.to_text` body and that
body references both `rt_enum_payload` and `rt_value_to_string`. The consumer
object instead calls `rt_to_string` immediately after `rt_enum_new`; it never
references the emitted custom method. This proves the remaining mismatch is at
the consumer call target, not in enum payload construction, arrays, rows, or
the provider method body.

The Rust LLVM `Call` and `MethodCallStatic` runtime-shortcut paths were audited
because both contain leaf-name redirects for `to_text`. Two declaration/owner
precedence candidates passed focused Rust unit contracts. A freshly built Rust
driver also typechecked the LLVM feature. However, a retained Phase 3 probe
with that driver supplied only as `--runtime-path` remained byte-for-byte red:
the Phase 3 executable's embedded `rt_native_build` provider still performs
codegen, while `--runtime-path` selects worker/link artifacts and does not
replace that embedded provider. The Rust candidates were therefore removed;
they were not admitted or pushed without a source-matched Phase 3 capsule.

The next bounded step is exact: build `libsimple_native_all.a` from the audited
Rust candidate, relink only the retained Phase 2/3 compiler capsule against
that archive, then run the direct imported-enum probe once with a fresh cache.
Do not run a full bootstrap. This session reached the mandatory three-cycle
cap, so no further candidate or probe was attempted.

## Resolution evidence (2026-08-09)

The retained-object diagnosis was correct. LLVM's `Call`,
`MethodCallStatic`, and emitter paths redirected qualified imported user
methods by leaf name, so `DbValue.to_text` became `rt_to_string` even though
the provider object defined the correct canonical method body. Runtime method
shortcuts now require a built-in receiver owner; qualified user owners retain
their canonical call target.

Focused Rust contracts pass for built-in/custom owner classification and for
both direct and static imported calls. The targeted provider archive is
`libsimple_native_all.a` SHA-256
`85b0a2ecc74e6561a6af91b3a62c3c1e26105289ad6622cd739f02bf10fc14db`.
A retained pure-Simple Phase-2-derived capsule was relinked against it without
a full bootstrap; the resulting compiler SHA-256 is
`675aea587fecd764411390a303627c2017dc1f6a92bf45ecca68d670af4b977e`.

With fresh caches and `SIMPLE_NO_STUB_FALLBACK=1`, both
`native_imported_enum_text_payload_probe.spl` and
`native_imported_struct_array_argument_probe.spl` compile and print their
exact PASS markers. Neither emits the runtime ABI guard or SIGSEGV. The C
runtime additionally proves array registry ownership before dereferencing a
header and emits at most one bounded `[simple-runtime][error]` record for a
heap-tag-colliding scalar; its direct contract passes for `9`, `17`, and `-7`.
