## C37 ordinary-route follow-up (2026-10-11)

C37 producer `35d099` compiling frozen source
`67137f4fb7c5856d39717576e4c2ef84a4deeca7`, deferred entry, completes
HIR/MIR for 96 modules and emits 77 real objects, but rejects 19 declaration-only
dependencies. Evidence: manual-next-source-c37-producer/deferred/build.log and
result.json beneath the same phase3-whole evidence root below. No fabricated
objects or fallback were enabled. The earlier streaming-only fix is insufficient.

The harness explicitly sets SIMPLE_BOOTSTRAP_STAGE3=0 and STAGE4=0. This selects
ordinary retained parsing, which did not capture the persisted proof. After HIR,
driver_orchestration.spl calls evict_ast() under --low-memory, clearing modules.
The native predicate then has neither retained AST nor a proof. This causal route
is visible in source; no instrumented runtime proof dump has been claimed.

The follow-up captures the same strict declaration predicate from successful
ordinary native low-memory phase-2 parser output, binding each row to module, canonical source path,
and SHA of the exact parsed source bytes before source reclaim. The new map
replaces prior rows, and phase-2 entry resets it. Failed parsing cannot publish
ordinary proof. Existing streaming capture and native empty-MIR/data/identity
guards remain unchanged. No AST is retained longer and no extra parse is added.
Interpreter/check and ordinary non-low-memory routes do not incur this extra
parser scan or hashing; their existing retained-parser behavior is unchanged.

Cold and warm lifecycle: the ordinary parse loop calls the same selected frontend
provider on both a cold parse and a validated frontend-cache hit. Proof capture
occurs after that loop commits. A HIR cache hit happens later, after this capture,
so it does not bypass the proof boundary. Parse-shard workers only contribute
their owned parser entries; a missing parser entry cannot acquire proof.

Authored controls exercise the actual capture helper with parsed type/facade/
extern/empty positives, real nonextern function/constant/executable/trait-body
negatives, AST eviction, stale identity, and replacement by an empty current
inventory. They are unexecuted during the capacity hold. Required native follow-up
is the failed deferred entry with --low-memory, stage3/stage4 disabled: cold cache
and warm frontend/HIR cache; both must record legitimate objectless dependencies,
retain all real provider objects, and refuse lost-body/data negative fixtures.
Changed-source warm-cache negatives must reject stale proof. No actual native or
whole Phase3 PASS is claimed. Collect reviewed fixes on release_phase3; do not
push that branch until actual Phase3 PASS.

## Observed failure

C36 producer SHA256 5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235 compiling frozen source f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c, deferred_deserialize entry, ARM64 LLVM --entry-closure --low-memory: all 7 modules complete MIR; five real objects are retained, but lib.string_core and compiler.frontend.ast fail `MIR module has no functions or static data`.

Evidence root: /home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/deferred-deserialize. build.log lines473-487; retained-object-inventory.json; ICE receipt /home/yoon/dev/simple-c36-manual-consumers-20261011/build/ice/3107890_n2674577367026128815/ice_receipt.tsv.

## Source trace

lib.string_core has an export-use plus export names; compiler.frontend.ast has six structs and one enum, no functions/constants. Both already satisfy C36 driver_native_module_is_export_facade when the ParserModule is retained. Commit632080a1b7839b2cff1299bf2ca8ab01fa6f7e50 only removes the positive import/export/type witness for parser-confirmed empty files; it does not fix parser absence.

Streaming parsing explicitly clears ctx.modules (driver_source_pipeline_parsing.spl:777), and streaming HIR clears it again plus evicts source contents/module surfaces (driver_hir_pipeline_lowering.spl:1050,1076). Native phase only invokes the objectless predicate behind ctx.modules.has(name) (driver_aot_native_output.spl:1993). Thus the current safety proof is lost before it is consumed. This is a source-level causal diagnosis; no instrumented runtime ParserModule dump has been claimed.

## Required correction

Capture a compact parser-validated declaration-only proof before transient parser release, bound to exact module/physical path/frozen content identity. Retain only this proof through HIR/cache/AST eviction and require both it and empty MIR functions/statics/constants at native admission. Reset proof per source-loading generation; missing/mismatched/cache-old proof must fail closed. Retain rejection of non-extern functions, constants, executable statements/classes/impls and other executable declarations. No fake object, empty-MIR-only inference, AST retention or global memory-policy rollback.

Regression matrix must cover facade/types, parser-confirmed empty module separately, non-extern function, constant, executable declaration, missing proof, stale source identity, HIR cache hit, and object-cache hit. New producer execution is deferred until the coordinated compiler-fix batch.

## Candidate and cache lifecycle

Issue: https://github.com/ormastes/simple/issues/3028. Candidate layers on the parser-confirmed-empty change632080a1 (locally eee37717). Extracts its declaration predicate into a driver leaf receiving the existing reference-owned ModuleSurfaceParserOwner, avoiding an extra full parser aggregate copy in phase2. Captures a positive proof only after parse/surface validation and successful transient scope closure/builder admission. Key is length-prefixed module name plus canonical source path; value is SHA256 of the exact parsed input. Hashing is limited to eligible modules. The context field is appended with a default, preserving existing field offsets.

Proof resets when the phase1 source inventory is published and on entry to streaming parse. Every streaming phase2 source is parsed/surface-validated before HIR cache lookup, so HIR cache hits acquire fresh parser proof. Native object-cache lookup follows objectless classification; stale cached objects cannot create proof. Full warm provider paths that skip phase2 have no proof and retain their existing typed-outcome authority; the fallback is fail-closed. Neither HIR/parser reclamation nor module surface eviction is changed. Source lookup rejects duplicate module/path ownership; digest mismatch is refused. No source reread in the native hot path.

Tests are authored but NOT executed: native_objectless_proof_spec covers type-only/empty acceptance after parser eviction, absent proof, changed source, alias collision, lost function/constant/impl rejection, and nonempty MIR data. Required follow-up before acceptance: compile/check the candidate with the coordinated next producer, run actual streaming cold+HIR-warm object probes for both original failing dependencies, and native negative controls. This source candidate is not a native/compiler verification PASS.

## Review refinement: defaults and executable trait bodies

Persisted proof conservatively refuses nonempty trait method bodies, using the same `method.body.stmts` test as module_surface_declarations:93. The legacy retained-parser compatibility path remains unchanged. Struct field defaults are deliberately accepted: HIR _Items/declaration_lowering:687-698 stores has_default/lowered expression in HirField; MIR _MirLowering/module_lowering:1759-1772 imports relocated provider field/default metadata into consumer owners and :1950-1961 records default expressions; _MirLoweringExpr/switch_operators_calls:5101-5119 emits the actual expression at an omitted-field constructor use and rejects Error defaults. There is no standalone provider object implied by that metadata. The actual frontend.ast dependency contains [] and false defaults, so blanket refusal would preserve the reported defect. Independent reviewer verified this ownership trace. Added parsed-source positive default-field and negative trait-body controls; execution remains deferred.
