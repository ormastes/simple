# Stage 3 native compiler corrupts cross-file parser state

Status: OPEN — release blocking

The provenance-gated Cranelift bootstrap builds and sanity-checks Stage 2. The
original Stage-3 failure corrupted parser state across the first source-file
transitions, pinned one CPU, and doubled retained memory to about 33.7 GiB.
That runaway is resolved. The current candidate parses, promotes, commits, and
releases 140 physical module surfaces in about 32 seconds with exact token
fields and no runaway RSS. Stage 3 now fails at the surface-owner handoff: the
streaming parse returns success, but the caller observes
`CompileContext.module_surfaces == nil`.

Two batch-debugger reproductions identified successive array-backed mode-cache
faults:

1. `ast_gen_harden_enabled` from `_ast_harden_retire_snapshot`;
2. `expr_env_mirror_enabled` from `expr_env_mirror_clear`.

The first cache was removed in favor of one scalar reset decision. The second
was replaced by scalar cached state plus an interpreter fallback, preserving
the native O(1) hot path. Subsequent bounded debugger cycles also repaired the
declaration/statement scalar mode caches and a released
`lex_inline_source_slot` backing.

The short-token interner was then found to retain strings allocated in a
per-file transient scope. `core_token_text_intern_reset()` now replaces that
owner before each lexer initializes, preventing a later source from consulting
the prior scope's released strings. A focused five-module streaming-surface
probe remains bounded after that repair. However, the exact 888-module entry
closure still reproduces the third-file CPU/RSS blowup, so the interner defect
was real but was not the sole root cause.

A debugger interrupt then identified the runaway stack exactly in
`aspect_registry_reset_module`: the aspect/effect/layer registries retained
transient keys across file teardown. They now rebuild one complete per-file
snapshot and promote every registry root while the scope is paused. A
behavioral regression owns two reclaimed scopes and selective reparse.

The next breakpoint proved `lex_next_snapshot()`'s heterogeneous
`[i64, i64, i64, text]` carrier decoded kind `FN` as `STRING_LIT` and decoded
line/text as nil. `LexNextSnapshot` is now a typed record; Stage 3 subsequently
parsed real source successfully.

Finally, post-teardown path canonicalization collapsed a valid symlink alias to
the workspace root. Streaming parsing now freezes one ordered canonical-path
inventory before opening any transient scope. The alias collision is gone.
The last observed failure is the copied `streaming_ctx` surface commit; source
now commits `Some(finished_surfaces)` directly through `self.ctx`. This final
owner correction is statically clean but intentionally unexecuted because the
three-cycle limit is exhausted.

Evidence:

- `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
- Stage-2 closure: 888 logical modules; the current run reaches 140 physical
  `parse-done` / `surface-done` / `promote-done` / `commit-done` / `released`
  sequences before the unverified context-owner handoff.
- Admitted parent SHA-256:
  `83d9076a8b80ecf8e50e13feb4fd65e881bf65dfa40a53c6b89a061f19c4136b`.
- Rebuilt Stage-2 SHA-256:
  `266217f9062fdca5642e19aed68a17c0fdfae19f4284a062236512043d508c61`.
- The bounded final run was stopped with SIGINT at 4.38 GiB and exited 130;
  its cache and log remain intact.

The three-cycle limit is exhausted for this session. Resume only the preserved
cache-backed bootstrap in a fresh scoped session. First verify that the direct
`self.ctx.module_surfaces` commit reaches
`lower_and_check_streaming_surfaces_impl`; if it does not, interrupt once at
the return/assignment boundary and inspect the exact value carrier. Never fall
back to the Rust seed for acceptance.

## 2026-08-20 continuation: tuple carrier and boolean epilogue

A fresh debugger cycle proved that the lowerer received the runtime `None` tag
at `CompileContext.module_surfaces`, even though `ModuleSurfaceBuilder.finish`
completed. Production streaming orchestration now commits the surface owner in
place and carries only a boolean across the phase boundary; the legacy tuple
surface remains compatibility-only.

The first canonical rerun then reached all 140 physical surfaces but returned
`parse_ok=false`. Native disassembly at the success epilogue showed a separate
receiver-lowering defect: code loaded the `CompileContext` receiver, overwrote
that register with the `CompileContext.has_errors` function address, and called
the method with a stale argument. The source now owns an explicit
`phase_had_error` scalar initialized before the hot loop and updates it on each
recoverable parse error. The success epilogue no longer relies on the malformed
receiver call. This is a source-level containment, not evidence that the
general native receiver-lowering defect is fixed.

The next two bounded reruns showed that a local boolean is not a safe
containment in this method either. Native code kept `%rbx` as the tagged
`CompilerDriver` receiver from the prologue, then used that same nonzero value
as `phase_had_error` in the success epilogue; the source-local `false` had no
independent storage. Both runs therefore returned false after all 140 surface
commits. The pending containment compares the authoritative scalar
`self.ctx.error_count_value` field directly with zero. It is intentionally not
executed in this continuation because the mandatory three-cycle cap is now
reached. The next scoped session must inspect that one generated epilogue
before any full bootstrap rerun.

## 2026-08-20 continuation: retained source inventory

The direct `error_count_value` epilogue generated correctly and exposed the
first previously masked diagnostic. A debugger break on `CompileContext.add_error`
showed source index 151 entering alias admission with `path=""` and
`module_name=""`; both values were nonempty when the canonical inventory was
frozen before the first parse scope. Thus the per-file teardown was reclaiming
strings reachable from a later `SourceFile` descriptor.

Streaming phase 2 now opens one empty transient scope, pauses it, and promotes
the complete `self.ctx.sources` owner graph before any per-file parse scope.
This is one bounded O(source-count) traversal and retains the original source
bodies without duplicating them per alias or per parse. The existing lifecycle
spec exercises a physical source plus a later alias through the new in-place
commit surface.

The first rerun showed that promoting `self.ctx.sources` as one root was
insufficient: `SourceFile` is a raw value record allocated before the active
scope, so the promoter could retain the outer array but could not discover its
record fields. Index 151 still arrived with empty metadata. The corrected owner
layout freezes paths, authored paths, bodies, module names, and canonical paths
into parallel text arrays, promotes those traversable arrays once, reconstructs
each per-file record from them, and rebuilds `self.ctx.sources` for phase 3.
This retains O(total source bytes + source count) storage and avoids deep-copying
the 888 logical source bodies.

The bounded third run reached the second physical source and failed after
`promote-done` but before `commit-done`. This proves the SoA inventory survives
phase entry but does not yet prove the reconstructed `SourceFile` value survives
the by-value `add_streaming_module_surface` / `builder.add_surface_canonical`
boundary. The next fresh cycle must break on the first `CompileContext.add_error`
and inspect only that add result and its scalar source fields. Do not repeat a
full run before resolving whether the record copy is allocated inside the
active transient scope.

The next debugger cycle showed `add_streaming_module_surface` returning
`Err(nil)` at source index 1 after `promote-done`. Removing `SourceFile` from
the persistent builder API did not move the failure. The remaining violation
was registry mutation while the parser scope was paused: pause enables graph
promotion but does not authorize new persistent builder allocations. Phase 2
now promotes the compact surface, ends/reclaims the transient scope, and only
then mutates `ModuleSurfaceBuilder` and constructs its return result.

A second-call builder breakpoint then proved the retained-array assumption
wrong: `canonical_path` remained valid, but the scalar `module_name` argument
was already an invalid `0x31` handle before builder code ran. Retaining an array
of borrowed handles is not ownership. The inventory now creates independent
text values with `rt_bytes_to_text(value.bytes())` before any transient scope.
Large source bodies are copied once per canonical physical path and reused by
logical aliases, keeping memory proportional to physical source bytes.

The final bounded run emitted a valid error string and proved those copies were
still made too late: phase 2 observed `SourceFile.module_name=""` before copying,
so both first and second files were indexed under the empty name. The canonical
owner has moved to phase 1. `CompileContext` now carries four independently
allocated scalar arrays for paths, authored paths, deduplicated physical
contents, and logical module names. Phase 2 consumes only those arrays and never
re-reads a `SourceFile` field. This final owner-boundary correction is static-only
because the three-cycle cap is reached.

## 2026-08-20 continuation: imported statement-tag comparison

The phase-1 scalar owner correction advanced the canonical Stage-3 build to
source sequence 253. It then stopped at
`src/compiler/mir_opt/mir_opt/pattern_dispatch.spl`: resident memory grew from
about 3.1 GiB to 14.9 GiB in roughly 80 seconds with no source progress, so the
run was interrupted under the resource guard.

A debugger break on parse call 254 proved the path and module name were valid.
After ten seconds, the stack contained 22 nested
`convert_flat_stmt_in_list -> convert_flat_if_stmt -> convert_flat_stmt`
frames while converting the long `elif` chain in `idiom_for_intrinsic`.
`convert_flat_if_stmt` already has an iterative `elif` walker, but it selected
that path by comparing against imported module-level `STMT_IF`. This is the
same Stage-3 imported-value misread family: the test missed nested arms and
recursively copied the remaining statement tree at every level.

The constant-owning AST module now exports `stmt_tag_is_if(tag)`, and both
Flat-AST bridge comparisons call that owner-local predicate. The correction is
source-level until one bounded canonical rerun advances beyond source 254
without the prior multiplicative RSS growth.

The bounded canonical rerun confirmed the memory-amplification part of the
diagnosis: at 53 seconds RSS was about 573 MiB, at 100 seconds about 529 MiB,
and at 168 seconds about 560 MiB, rather than the prior 14.9 GiB growth. It did
not advance beyond the `pattern_dispatch.spl` parse-start marker within three
minutes. The process was terminated cleanly under the runaway guard. Therefore
the owner-local tag predicate removes the multiplicative copying symptom but
does not yet prove forward progress; the residual finite-work stall needs one
fresh, scoped profiler/debugger cycle before another bootstrap attempt.

The fresh diagnostic also separated two executables that must not be confused:
invoking `stage2-runtime-authority/simple` directly identifies it as the Rust
bootstrap seed and reaches the Rust native-project linker. Its thread stacks
are not self-hosted parser evidence and are excluded from admission.

Static inspection established a stronger parser-owned invariant. The parser
rebuilds an `elif` chain from its tail; consequently each nested `STMT_IF` is
an older, strictly smaller statement index. The Flat-AST bridge now enforces
that monotonic order and a `stmt_count()` walk ceiling before arena access, so
corrupt/cyclic input fails loudly rather than spinning. The arena-owned tag
predicate also compares the frozen statement wire tag to literal `6`, avoiding
the Stage-3 module-constant load defect even inside the owning helper.

The next canonical run disproved the cross-module helper boundary itself. The
real self-hosted Stage-3 candidate reached source 254, never entered the new
iterative-walker guards, and grew to 9.6 GiB RSS at two minutes before bounded
termination. Therefore the call to the arena module's predicate was mislowered
before its literal comparison could run. The frozen `tag == 6` predicate now
lives in `convert_nodes.spl`, immediately beside both dispatch sites. This
removes both imported-state and cross-module-call dependencies from the hot
branch while retaining the monotonic-index and live-count guards inside the
iterative walker.

The third bounded cycle showed that moving the predicate was insufficient: the
self-hosted candidate reached source 254 and grew to 4.8 GiB RSS by 92 seconds,
again without entering the iterative guard. The process was interrupted at the
mandatory cycle limit. Both dispatch sites now compare their already-loaded tag
directly to frozen wire value `6`, with no constant import and no helper call.
This final correction is deliberately static-only until the next fresh turn.

The fresh self-hosted debugger cycle captured the remaining shape precisely:
19 nested `convert_flat_if_stmt` frames alternated with
`convert_flat_stmt_in_list`, all below one `convert_decl_fn`. Thus the outer
literal dispatch works, but the combined
`else_stmts.len() == 1 and stmt_get_tag(...) == 6` test classifies a real nested
arm as terminal and recursively converts it. The cardinality and tag checks are
now separate scalar branches with a `next_if` sentinel; no helper, imported
constant, or compound short-circuit expression remains on this boundary.

That split still reached 5.4 GiB RSS at source 254 in the third bounded cycle.
The parser proves every real nested arm is stored as a singleton `elif_else`
array, so the residual boundary is the imported array value itself. The elif
arena now exposes `elif_get_single_else_stmt(idx) -> i64`; the bridge decides
iteration from that scalar and retrieves the full array only for a genuine
terminal else. This removes the per-arm cross-module array copy/cardinality
read and is static-only until the next continuation.

The first scalar-projection run still reached 6.0 GiB RSS at 99 seconds. Its
implementation copied `elif_else[idx]` into a local array before returning the
scalar, so it had only moved—not removed—the hazardous nested-array operation.
The elif arena now maintains a parallel `elif_single_else_stmt: [i64]` at
`elif_new` time and clears it with the other AST arenas. The projection reads
only that bounded scalar array and returns `-1` for an invalid/stale index; no
nested-array copy or cardinality read remains on the Stage-3 bridge path.

The parallel elif-arena scalar still crossed a fresh module accessor and the
next bounded run reached 2.9 GiB RSS at 84 seconds. The parser now binds the
already-known singleton tail directly into a parallel field of the `STMT_IF`
record via `stmt_if_stmt_with_single_else`. The bridge reads it through
`stmt_get_if_single_else(current)`, beside the existing stable statement tag,
type, and body accessors. Legacy construction remains fail-safe with `-1`; the
production parser supplies the exact scalar while it still owns `tail`.

The statement-field run still reached 5.6 GiB RSS at 97 seconds. Its parser
population used a mutable `single_tail_stmt = -1` local followed by conditional
assignment, the same Stage-3 local-scalar defect previously proven for
`phase_had_error`. Parser construction now branches on `tail.len()` and passes
`tail[0]` directly to `stmt_if_stmt_with_single_else`; terminal arms call the
legacy `-1` constructor. No mutable scalar carries authority across the branch.
This correction is static-only at the mandatory third-cycle limit.

The direct-construction run still reached 5.2 GiB RSS at 94 seconds. An
environment-gated trace was invisible inside the self-hosted process, so the
third cycle temporarily emitted the decision scalars unconditionally and was
stopped at 9.9 GiB. It proved the stored chain is correct: for example the
candidate sequence is `81 -> 80 -> 79 -> ... -> 76`, each candidate has tag 6,
and each elif record has one else element. The iterative walker recognizes the
sequence, but conversion then recursively replays every remaining prefix
(`80..76`, then `79..76`, and so on). Therefore the residual amplification is
through the per-arm `stmt_get_body(current)`/then-body conversion, not elif
classification. The temporary print has been removed. The next scoped cycle
must inspect the then-body indices/tags before changing representation again.

The bounded body trace found the duplication before source 254. At source 155,
an authored one-statement arm was stored with `len=2`; its first element was
the authored expression while the nested candidate was also reachable through
the body inventory. Prefixes such as `284 -> 283 -> 282` were consequently
reconverted combinatorially. The parser had inserted `parse_block()` arrays
directly into `arm_body: [[i64]]`, allowing later tail mutation to share nested
backing storage. `parser_owned_stmt_list` now copies scalar statement indices
into a fresh array before every arm-body and terminal-else insertion. The
temporary body trace has been removed.

The independent-copy run still reached 5.9 GiB at source 254. A final bounded
second-element trace then proved physical duplication: examples include
`current=77`, body second element `76`, and nested candidate `76`. Copying an
inner array was insufficient because inserting it into `arm_body: [[i64]]`
reintroduced shared nested storage. `parse_if_stmt` now owns a scalar SoA body
inventory: one flat `[i64]` plus per-arm offset/count arrays. Rebuild creates a
fresh body from that scalar slice exactly once per arm. No nested array exists
during collection, and the temporary trace has been removed at the cycle cap.

The parser-only SoA run still reached 5.0 GiB at source 254, proving the same
nested-owner defect persisted in the canonical statement arena itself:
`stmt_body: [[i64]]`. Statement bodies now use one append-only scalar
`stmt_body_flat` arena plus per-statement offset/count arrays. Every constructor
stores scalar indices through `stmt_body_store`; `stmt_get_body` validates the
range with subtraction-based bounds and reconstructs one independent body for
the consumer. Snapshot/traversal code now uses that accessor. The legacy nested
array remains only as an allocation-shape compatibility field and is no longer
read or mutated after allocation.

This correction passed the entire 609-source Stage-3 parse with bounded RSS
(about 0.49--0.58 GiB), eliminating the source-254 failure. The run then
reported `n_modules=0`, completed HIR at the same timestamp, and failed phase 4.
The compact surface registry had been assigned only through nested
`self.ctx.module_surfaces`, which did not persist across the native receiver
boundary. `CompilerDriver` now directly owns the finished streaming registry,
a readiness scalar, and the pre-parse entry index. Streaming HIR selects that
owner directly and reconstructs each `SourceFile` from the phase-1 scalar SoA
arrays rather than reclaimed record fields.

The third bounded bootstrap cycle confirmed that the direct driver owner
survives the native receiver boundary: Stage 3 again parsed all 609 sources,
then performed real per-file HIR work for retained modules instead of reporting
an empty registry. It reached `phase3:hir_typecheck:done` at +175895 ms and
entered monomorphization. Phase 4 then failed closed with
`Module surface/source fingerprint mismatch for
src/compiler/frontend/core/aop.spl`. This is the next exact blocker: the
streaming surface registry is now present, but at least one retained surface is
paired with source bytes whose phase-4 fingerprint does not match the phase-2
binding. No fourth bootstrap was started in this session; the mandatory
three-cycle cap was reached. The next cycle must trace the stored surface
fingerprint and reconstructed source identity for that one module before
changing ownership again.

The next turn's three bounded cycles refined that failure. Replacing the large
`ModuleSurface` value copy with the existing scalar identity boundary did not
remove the mismatch. A component-level diagnostic in the third and final run
proved that the retained bytes are not stale or corrupt:

```
index=69/70
path='.../src/compiler/10.frontend/core/aop.spl'/'.../src/compiler/10.frontend/core/aop.spl'
module='compiler.frontend.core.aop'/'compiler.10.frontend.core.aop'
length=25391/25391
hash=0/0
```

The second source is a compatibility alias for the same canonical physical
file. `ModuleSurfaceBuilder.add_alias_canonical_identity` already proves the
canonical path, content length, and content hash before binding that alias to
the physical surface. Streaming HIR nevertheless applies the stricter
original-source index/module predicate when the canonical surface was not
stored in `lowered_by_surface` (for example after its lowering is poisoned), so
the alias produces a false fingerprint failure that masks the earlier module
diagnostic. The next correction must distinguish physical-surface integrity
(canonical path, length, hash) from alias routing identity, and must not retry a
poisoned physical surface under an alias spelling. No fourth bootstrap was
started.

The alias-aware correction now validates compatibility aliases by physical
path/content identity and records a poisoned physical-surface index so aliases
cannot retry it. This removed the `aop.spl` false mismatch: Stage 3 advanced
from 33 to 369 successfully retained HIR surfaces and traversed the remaining
source inventory before phase 4 failed. The first surface without a
`phase3:hir:file:done` receipt is
`src/compiler/backend/backend/native/mach_inst.spl`.

Two bounded diagnostics classified that new boundary. Neither
`[hir-owner-fatal]` (the `lower_result.is_err()` branch) nor `[hir-fatal]` (an
unrecovered `LoweringError`) appeared in cycles two or three. Therefore the
only branch capable of dropping the otherwise successful HIR aggregate is the
post-collection comparison
`self.ctx.error_count_value > module_errors_before`. From `mach_inst.spl`
onward the successful-module count remains 369 while later modules are still
parsed/declared, consistent with a stale or mis-lowered baseline scalar causing
every later module to inherit an earlier context error. The next correction
must make `_driver_collect_hir_errors` return a module-local fatal count and
use that result as the poison decision; it must not infer module-local failure
from a before/after read of the large mutable `CompileContext`. No fourth run
was started after this three-cycle result.

The following three-cycle audit confirmed that conclusion. The alias-aware
path consistently reaches 369 retained HIR surfaces and the first missing
completion remains `backend/native/mach_inst.spl`. Adding unconditional output
at both legitimate failure owners produced neither `[hir-owner-fatal]` nor
`[hir-fatal]`; phase 4 still failed after later sources were parsed and
declared. Thus no parser/scope/promotion failure and no module-local fatal
lowering diagnostic exists at that boundary. The streaming loop's sole
remaining drop condition is the global context error-count delta.

The non-streaming loop already contains the correct owner pattern: keep the
`LoweringError` aggregate inside `HirLowering`, read
`lowering_error_count()`, `lowering_error_message_at()`, and
`lowering_error_is_recovered_at()` as scalar/text projections, accumulate one
module-local fatal count, and poison only when that count is nonzero. The next
cycle must mirror that pattern in `lower_and_check_streaming_surfaces_impl` and
delete its `module_errors_before` / global error-count comparison. No fourth
bootstrap was started.

The module-local diagnostic correction is now in place and exposed the hidden
semantic failures from the beginning of HIR, rather than first at source 369.
Representative fatal names are `OptimizationLevel`, `ContractMode`, `Token`,
`Logger`, and `Bitfield`; they arise while imported/package-sibling callable
and type surfaces are eagerly materialized. A broad attempt to resolve every
composite field dependency through the owner's full import graph was rejected:
it introduced real same-name conflicts (`Span`, `TraitBound`, `TraitDef`) and
still missed the original types. That change was reverted. A narrower
callable-only import-route attempt avoided those conflicts but still did not
resolve `OptimizationLevel`/`ContractMode`, proving the needed owner route is
not preserved at that late consumer boundary; it too was reverted.

The next bounded diagnostic must identify the exact `ModuleSurfaceCallable`
owner and parameter/return dependency that emits each unresolved name. The
robust correction is to freeze the dependency's terminal module/item binding
when the callable surface and import routes are built, then consume that frozen
binding during eager signature materialization. It must not infer provenance
from a consumer's flat symbol table or search all same-named declarations.
The final cycle was stopped after the early repeated fatal proved the narrow
route ineffective; no fourth bootstrap was started.

The next three-cycle probe identified the exact callable owner. The repeated
`OptimizationLevel` failures come from
`compiler.70.backend.backend.llvm_backend` methods `create`,
`create_baremetal`, `compatibility_build`, and `create_wasm`. That surface has
18 aligned imports/routes; route 2 is the explicit five-item
`compiler.backend.backend.backend_types` import and resolves to terminal surface
56. Thus the producer retained the route correctly.

The remaining failure was namespace projection: registering the selected
terminal declaration binds `backend_types::OptimizationLevel`, while
`declared_imported_surface_callable_type` deliberately queries the callable
owner's qualified namespace (`llvm_backend::OptimizationLevel`). The explicit
callable dependency resolver now binds that owner-qualified alias to the same
terminal `SymbolId`; it does not create a second declaration or perform a
flat-global lookup. Trait method signatures likewise now resolve through the
trait's physical surface rather than the implementing type's module, which is
the corresponding `ContractMode` owner defect. These final edits are statically
clean but remain unexecuted because the third bounded bootstrap cycle had
already reproduced the pre-alias result; no fourth run was started.

The following turn ran three further bounded verification/fix cycles. First,
the owner-qualified alias logic was still absent from imported *free-function*
registration: methods materialized their signature dependencies, while the
`imported_mod.callables` branch lowered its callable type immediately. Moving
the same materialization immediately before free-function signature lowering
advanced HIR through the driver family with neither `OptimizationLevel` nor
`ContractMode` failures. At source 150 it then exposed an unqualified
`Effect` collision: signature dependencies had been registered under their
short names, incorrectly making `mir_effects.Effect` compete with
`hir_types.Effect`. Signature-only dependency registrations now use canonical
owner-qualified internal keys, preserving the consumer's unqualified scope.

That correction retained the `ContractMode` fix, but the third cycle showed
`OptimizationLevel` still unresolved. The terminal enum was defined under its
canonical internal key, yet its older Option-based `already_bound` branch did
not reliably publish the terminal qualified alias under the staged native ABI.
The explicit-import seam now retrieves the exact internal key with the
scalar-safe `lookup_or_invalid` API and binds both terminal and callable-owner
qualified aliases directly to that one `SymbolId`. This final correction is
statically clean but unexecuted: the mandatory three-cycle cap was reached and
the known-failed third process was terminated rather than starting a fourth
bootstrap in the same turn.

The next fresh three-cycle run isolated and fixed the remaining provenance
edge. The explicit `OptimizationLevel` route belongs to
`compiler.driver.driver_bootstrap`, whose named import targets the
`compiler.backend.backend_types` facade rather than the terminal declaration.
The resolver now follows exactly one canonical re-export hop inside that
already-selected explicit import and then binds the resulting terminal symbol;
it still performs no flat or global same-name search. The third run cleared
`OptimizationLevel`, `ContractMode`, and the prior `Effect` collision and
advanced cleanly to HIR 280/609.

At source 275 that run exposed a distinct bootstrap-surface failure: the one
source-level `assert` in MIR dynamic-module initializer naming desugared to
`__assert`, which is unavailable while Stage-3 HIR is building the compiler.
The invariant is now structural instead of runtime-asserted: the canonical
pure `mir_dynamic_module_init_name` helper always emits a module-qualified or
stable indexed fallback name. Its previous source-introspection test was
replaced with behavioral normal/fallback/non-bare cases. These edits pass
`git diff --check`; no fourth bootstrap was started after the mandatory third
cycle.

The next bounded sequence cleared the `__assert` initializer boundary and
advanced to source 464, where Flat-AST's unknown binary-operator fallback used
another source-level `assert false` and then unsafely returned `Add`. The
decoder now returns an explicit `BinOp.Invalid`; the existing HIR default arm
turns that sentinel into a fatal lowering diagnostic. Its source-introspection
test was replaced by direct known/invalid decoder behavior. A subsequent
source-502 `Type` failure exposed the direct-declaration twin of the qualified
publication bug: callable dependency registration now republishes the exact
internal-key symbol into its owner-qualified namespace with scalar-safe lookup.

With those corrections, Stage 3 lowered all 609/609 HIR modules with zero
fatal diagnostics. It then segfaulted immediately after the final module and
before source reclaim or any downstream phase marker. The first post-loop
operations copied the complete `CompileContext` twice (`summary_ctx`, then
`phase_ctx`), including all 609 retained HIR modules; the layout-validation
helper also accepted that context by value, so its `add_error` mutations were
discarded. The streaming completion path now mutates its canonical `self.ctx`
in place, removes both aggregate copies, and declares the validation helper as
`me fn`. This final post-HIR correction is statically clean but unexecuted
because the third bootstrap cycle had completed when it was identified.

The next turn confirmed the post-HIR ownership correction: Stage 3 emitted
`phase3:hir_typecheck:done` after 609/609 modules and entered phase 4 instead of
crashing. The first implementation used a top-level `me fn` validation helper;
the staged HIR surface lost all three parameter bindings, so it was replaced by
a pure helper returning `[text]`, with each canonical context committing those
diagnostics itself. That form again completed all HIR and reached phase 4, which
failed because the formerly discarded validation errors now correctly remain
in the context.

A late phase-4 probe using `CompileContext.error_message_at` reproduced a
segfault before printing any error, demonstrating that the freshly stored
diagnostic array is another unsafe aggregate boundary under Stage-3 native
value semantics. Reporting is now performed while each validation error is
still a local `text`, immediately before `self.ctx.add_error`, with a ten-row
bound and exact total. The fragile phase-4 array probe was removed. Three
cycles were exhausted; the next fresh execution must capture these exact
post-HIR validation failures and then repair the owning contracts.

The next three-cycle audit proved there were no post-HIR contract violations.
The pure helper returned zero errors, yet phase 4 observed a nonzero context
error count. Scalar-only checkpoints showed the count was exactly zero both
before and after the 609-module HIR-map commit. Transporting the three large
validation aggregates through the helper was also nondeterministically unsafe,
so the streaming owner now invokes all four validators and static weaving
directly, committing each local error immediately; that path completed with no
reported validation failures.

The remaining corruption occurs at the caller handoff. The streaming lowerer
is already a `me` owner operation that commits directly to `self.ctx`, but
`driver_orchestration` then assigned its returned whole-context snapshot back
into the same owner. Under Stage-3 native value semantics that redundant
aggregate reassignment changes the adjacent error scalar between successful
phase-3 completion and phase 4. The orchestration path now records whether HIR
is streaming/in-place and skips reassignment only in that case; legacy
non-streaming paths still install their returned context. This final handoff
fix is statically clean and awaits a fresh execution after the three-cycle cap.

The next bounded cycles confirmed the handoff diagnosis and advanced the
frontier again. Direct post-HIR validation completed without reporting any
error, but the redundant phase-4 `CompileContext.has_errors()` reconstruction
still rejected the already-admitted phase. `monomorphize_impl` now requires the
authoritative `analyze_ok` scalar produced immediately after all HIR validators;
both orchestration callers pass it explicitly. That removed the false failure
and entered the real monomorphization call.

The 609-module map then crashed in `run_monomorphization`. This is the
repository's documented bootstrap skip branch: native-path monomorphization
Phase B remains gated, while normal builds must run the real pass. Bootstrap
mode now activates the existing skip automatically from `SIMPLE_BOOTSTRAP=1`
instead of depending on a second unset variable; normal builds are unchanged.
The third cycle proved `phase4:monomorphize:done` and entered phase 5 MIR
lowering. It later segfaulted during a new module's struct-type prescan, after
successfully lowering `log_error`; the old trace named expression kinds but not
the owning module/function. Bootstrap-only before/after prescan receipts now
record module, function index, and function name so the next fresh execution
can identify the exact corrupted HIR body. No fourth cycle was started.

The following bounded cycle cleared that prescan frontier. The admitted Stage-2
compiler completed all 609 HIR modules, completed monomorphization, and lowered
MIR well past the previous crash. It then stopped while lowering
`compile_riscv_gen2_zca_migrating_predecode_product`: the last receipt was
`[mir-method-call] result-types method=CodegenError`. For 25 seconds the log
remained byte-for-byte unchanged while the process consumed one core and grew
from 37 GiB to 44 GiB RSS, so the exact child was terminated before host
exhaustion. The next statement called `rt_enum_discriminant(receiver.kind)`
even though the surrounding code already documents payload-enum discriminants
as invalid on the self-hosted native representation, and the only remaining
consumer used a guard already documented as dead. MIR method lowering now
removes that discriminant read and uses the conservative
`static_receiver_name == ""` recovery condition directly. This preserves
static-call behavior while removing the allocation runaway boundary.

The third and final cycle for the turn proved that removing the discriminant
advanced beyond the original `CodegenError` call, but the next untyped receiver
(`structural_sha256`) stopped at the same receipt boundary. Its log stayed
unchanged for ten seconds while RSS grew from 40.4 GiB to 42.5 GiB. The next
operation was the fallback `match receiver.kind` inside `lower_method_call`, so
the defect is the repeated payload match after the `HirExpr` aggregate crosses
that native call boundary. Static receiver name/symbol recovery now occurs
entirely in `expr_dispatch`, while the receiver is still in its canonical
owner; `lower_method_call` consumes only those scalar hints and no longer
re-matches the aggregate for static-owner discovery. This correction is
statically clean but intentionally unexecuted because the mandatory
three-cycle cap was reached.

The next turn's first cycle reproduced the same allocation signature one step
earlier on the resolved
`compile_riscv_gen2_zca_rv32_cjal_migrating_predecode_product` call: the final
receipt was `method-dispatch-before`, followed by ten unchanged log seconds and
RSS growth from 38.2 GiB to 40.3 GiB. `expr_dispatch` was inspecting every
method receiver for a possible static owner even when `MethodResolution`
already identified a resolved instance, trait, free, or static call. It now
classifies the resolution first and performs syntactic static-owner recovery
only for `Unresolved`. Resolved calls therefore never touch the nested receiver
payload solely for fallback discovery.

Cycle 2 rebuilt Stage 2 successfully but Stage 3 segfaulted immediately after
source closure and before the first surface receipt. The token-interner reset
was present, but it ran inside `lex_init_with_path` after the driver had opened
the per-file transient scope. That allocated the replacement global dictionary
inside the very scope reclaimed at file teardown. The reset now occurs in
`driver_end_transient_parse_scope` only after
`rt_transient_array_scope_end()`, alongside the existing load-bearing
post-scope `ast_reset`; the new interner owner is therefore process-lived while
the released file's cached strings are no longer reachable. Non-streaming
parses retain their normal process-lifetime cache.

The third cycle rebuilt Stage 2 with that lifetime correction but reproduced
the same immediate Stage-3 segfault. The final receipt is exactly
`source_closure 612/612 step 1/6 complete`; no phase-2 surface-start receipt is
emitted. This disproves interner-reset placement as the sole cause of the new
early failure and bounds the remaining defect to the phase-1 closure-to-phase-2
owner handoff (or an earlier corruption first observed there). The MIR
resolved-call guard remains untested in this cycle. No fourth execution was
started under the three-cycle limit.

Static inspection of that exact boundary found the same aggregate handoff
class already proven in phase 3: `load_sources_impl` copied `self.ctx` into a
local `CompileContext`, rebuilt the source-owner fields on that copy, returned
the whole context in a tuple, called aggregate `has_errors`, and the caller
assigned the returned snapshot back into `self.ctx` before emitting
`phase1:load_sources:done`. The streaming path now commits all source inventory
directly to its canonical `self.ctx`, derives success from the maintained
`error_count_value` scalar, and the caller skips the redundant whole-context
assignment only for streaming mode. Legacy non-streaming compilation retains
the returned-context installation. This correction is statically clean and is
intentionally unexecuted after the three-cycle cap.

The next cycle confirmed the phase-1 correction: Stage 3 entered phase 2,
processed all 612 surfaces, completed 612/612 HIR modules, and entered MIR.
The next allocation loop ended at
`method-dispatch-before method=CodegenError`; ten unchanged log seconds grew
RSS from 34.9 GiB to 37.1 GiB. The added caller-side `match resolution` was the
only operation between that receipt and `lower_method_call`, proving that a
second match on either nested payload is unsafe after extracting the outer
`MethodCall` value. The MIR caller now transports `receiver`, `resolution`, and
arguments without reinspection. Resolved calls preserve their authoritative
resolution; unresolved static calls use the existing conservative unique
symbol recovery. A future HIR schema extension must carry explicit scalar
static-owner metadata to recover ambiguous unresolved static calls without
reintroducing nested payload matching.

Cycle 2 proved that transport boundary: the previously failing long RISC-V
call and `structural_sha256` both completed MIR dispatch. `CodegenError` then
froze after `option-dispatch` and before `enum-owner`; ten unchanged seconds
grew RSS from 36.3 GiB to 38.5 GiB. The next operation was another
`match receiver.kind`, used for enum-constructor reclassification. Enum
construction now uses an existing scalar owner hint or, only for uppercase
variant-shaped names, a conservative unique owner search. The adjacent GPU
`this.index/thread_index/group_index` probe likewise no longer matches the
nested receiver; those closed pseudo-methods lower only while the current
function has an admitted GPU kernel target. Ordinary methods outside kernels
retain normal dispatch.

Cycle 3 cleared all of those method boundaries: multiple `CodegenError`
constructors, `structural_sha256`, and the long RISC-V calls completed through
`resolution-arm`, owner lookup, and final write-back. MIR advanced through many
additional modules and then segfaulted at the older next-module prescan
frontier after fully lowering `log_bootstrap_flat_warning`; the final bytes are
three generic `[mir-prescan] HirExprKind.Block` receipts. The detailed
module/function prescan receipts were still gated by a late environment probe
that is false in this self-hosted phase, so they are now unconditional for the
next bounded diagnostic cycle. No fourth run was started.

The next run showed those receipts still absent while generic prescan messages
remained, and Stage 2 reported only four recompiled units. Static call-chain
inspection located a distinct bootstrap-flat prescan in
`_MirLowering/bootstrap_globals.spl`; Stage-3 bootstrap uses that path instead
of `lower_module`'s instrumented loop. The final successfully lowered function
was `log_warn`. The flat prescan now emits unconditional module index/name and
function index/name start/done receipts around its authoritative loop, so the
next run will name the exact failing HIR owner without depending on cache or
environment tracing.

## 2026-08-21 HIR retention root cause

The subsequent stable-source cycle bounded the earlier failure before MIR:
Stage 3 reached HIR 11/614 at 1.27 GiB RSS, 44/614 at 3.48 GiB, and 84/614 at
5.83 GiB. The run was terminated before host OOM. Independent runtime and
pipeline audits disproved the earlier outer-array-copy theory: native
`Array.push` grows one stable backing and stores a shallow value handle.

The dominant defect is the transient-scope order in
`driver_hir_pipeline_lowering.spl`. The scope was paused immediately after
parsing and before `lower_parser_module_unstub`. Native allocations made while
paused receive process scope zero, while scope teardown reclaims only objects
owned by the active transient scope. Consequently every discarded HIR lowering
temporary survived for the process lifetime, matching the measured roughly
60 MiB/module growth.

The source correction keeps the transient scope active through complete HIR
lowering, pauses only after the final module and diagnostics exist, then
promotes the canonical HIR graph, diagnostics, frontend registries, and the
newly committed private bootstrap-flat store row before ending the scope. The
store promotion API exposes no raw aggregate arrays and rejects absent or
misaligned publication. `HirLowering.begin_module` also clears module-local
`lowered_traits`, which previously retained full trait graphs across modules.
Cross-module value-layout validation and entry-module semantics remain intact.

This fix is statically clean and has focused behavioral owner/reset coverage.
It is not yet accepted: the session exhausted the three-cycle bootstrap limit
before this root-cause correction landed. The next authoritative action is one
admitted Stage-2 bounded prefix probe using the canonical Stage-3 closure and
isolated cache. Acceptance requires a sharply reduced HIR slope (target at most
8 MiB/module over indices 16..128) before another full bootstrap is attempted.

## 2026-08-21 phase-5 MIR: the variant-owner scan was the allocation runaway

Verdict on the phase-5 stall while lowering
`compile_riscv_gen2_zca_migrating_predecode_product`: **not a hang — an
unbounded-allocation cost problem**. The evidence recorded above is decisive
and rules out non-termination in the usual sense: the process kept one core
pinned and RSS climbed monotonically (37 -> 44 GiB in 25 s; 40.4 -> 42.5 GiB in
10 s; 36.3 -> 38.5 GiB in 10 s) with a byte-for-byte unchanged log. A
non-terminating loop that allocates nothing does not move RSS; this one moved
it by gigabytes per ten seconds. The loop makes forward progress and would
terminate — it simply cannot, because it exhausts the host first. The
distinction matters for the fix: no termination guard was needed, only removal
of the superlinear per-call work.

Root cause. The conservative enum-constructor recovery introduced when the
nested `match receiver.kind` was removed from `lower_method_call` replaced one
unsafe payload match with a nested scan over `enum_variant_index.keys()`:

    for enum_owner_name in self.enum_variant_index.keys():
        for enum_variant_name in self.enum_variant_index[enum_owner_name]:

That scan ran **once per method call** whose leaf starts uppercase and whose
static owner is unknown, materializing a fresh key array on every call. On the
609-module self-host closure `enum_variant_index` holds the whole program's
enums, and `compile_riscv_gen2_zca_migrating_predecode_product` is a dense run
of `CompileResult.CodegenError(..)` constructions — precisely the shape that
maximizes the scan. Under the phase-5 transient scope the per-call key arrays
are not reclaimed, which is the observed RSS slope. The receipt boundary in the
log (`option-dispatch` reached, `enum-owner` not) brackets exactly this scan.

Fix. `MirLowering.enum_variant_owners: Dict<text, [text]>` is the maintained
inverse index (variant leaf -> every currently registered bare owner), updated
by `reindex_enum_variant_owners` at each bare-key write in
`register_enum_variants` and at the two built-in `Result`/`Option`
registrations. The divergent last-wins eviction path withdraws the prior
owner's leaves, so an evicted registration cannot keep naming an owner. The
call site is now one dict lookup with the identical acceptance rule the scan
had — exactly one registered owner — so the recovery is neither more nor less
permissive than before. Per-recovery work goes from O(enums x variants) plus
one key-array allocation to O(1) with no allocation.

Files: `src/compiler/50.mir/mir_lowering_types.spl`,
`src/compiler/50.mir/_MirLowering/module_lowering.spl`,
`src/compiler/50.mir/_MirLowering/bootstrap_type_registration.spl`,
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`.

Reproduce/pin: `test/01_unit/compiler/mir/enum_variant_owner_inverse_index_spec.spl`
(4 examples, all passing) covers the unique-owner recovery for the exact
`CompileResult.CodegenError` shape, the two-owner refusal, eviction withdrawal,
and idempotent identical re-registration. Neighbouring MIR enum specs were
re-run; `enum_bare_name_collision_loud_miss_spec` is green, and the two
failures in `enum_bare_name_collision_dual_key_spec` (a Rust-seed source
assertion) and `mir_enum_variant_references_exist_spec` (a `MirTerminator.Return`
cross-spec reference scan) are pre-existing and untouched by this change.

Not fixed here, recorded instead:

- TODO(mir-trace-gating): `src/compiler/50.mir/**` currently carries 72
  UNCONDITIONAL per-expression `eprint("[mir...")` receipts (38 in
  `_MirLoweringExpr/method_calls_literals.spl`, 17 in
  `_MirLoweringExpr/expr_dispatch.spl`, the rest across
  `_MirLowering/{module,function,bootstrap_globals}_*.spl`, `mir_data.spl`,
  `mir_lowering_stmts.spl`). These are a real per-expression cost on the
  self-host closure and should be gated behind the existing
  `bootstrap_trace` / `SIMPLE_MIRB_TRACE` idiom (default off), NOT deleted —
  they are the live instrument this investigation depends on to name each
  frontier, and several were made unconditional on purpose for the current
  bounded cycles. Gate them once the phase-5/phase-6 frontier is cleared.
- No wall-clock before/after was captured. Two attempts to benchmark the scan
  against the index failed for environmental reasons, not for lack of trying:
  `bin/simple run` cannot resolve `MirLowering.new` outside the spec harness,
  and inside the harness the enum-population fixture exits with
  `executed=0`/`outcome=ERROR` before any example runs. The complexity claim
  above is therefore analytic plus the RSS slopes already recorded; a measured
  number should be taken from the next bounded Stage-3 cycle's phase-5 log.

## 2026-08-22 ARM64: ready scalar survived while surface owner was nil

A fresh admitted ARM64 Phase2 compiler parsed, promoted, committed, and
released all 665 Stage3 surfaces, proving the comparison-chain parser repair.
It then segfaulted immediately after `phase3:hir_typecheck:start`. LLDB pinned
the null dereference to
`CompilerDriver.lower_and_check_streaming_surfaces_impl +356`.

The first interpretation of that frame was wrong: the dereferenced register
was claimed to hold a newly constructed `HirLowering`. Full-function
disassembly and source mapping later proved it holds
`self.streaming_module_surfaces_owner`; the constructor result is stored in a
different stack slot. The short constructor call is exactly what the real
streaming implementation requests. A later method-owned experiment compiled
both changed call sites to their correct method symbol. There is no
call-target mis-resolution at this crash, so those ineffective changes were
removed.

The actual invariant break is `streaming_surface_owner_ready == true` while
the raw class-valued `streaming_module_surfaces_owner` is nil. The consumer
trusted the scalar and immediately dereferenced the raw owner. This confirms
the user-raised requirement: parsing/owner transfer can fail, so the value must
be checked for absence and only then unwrapped.

The driver owner is now `ModuleSurfacesByName?`, initialized/reset to nil and
committed as `Some(retained_surfaces)`. Phase 3 requires both the ready scalar
and a non-nil owner, then calls `unwrap()` only after that check. Regression
coverage owns both the normal retained-owner lifecycle and the adjacent
`ready=true/owner=nil` inconsistent state, which must return a diagnostic
instead of crashing. Acceptance requires a rebuilt admitted Phase2 and the
exact Stage3 HIR-entry run.

The first execution of that Option guard still crashed, 28 bytes later in the
same function. LLDB and disassembly proved the Option tag was `Some`, but
`rt_enum_payload` returned nil; the next dereference was the progress read of
`surfaces.surfaces.len()`. The consumer now also checks the unwrapped payload
before use, covering the exact `Some(nil)` state.

The producer-side cause is a nested class-valued Result carrier in
`module_surfaces_by_name_from_parts`: `module_surfaces_freeze(registry)` mutates
the class owner in place, then source unwrapped its Result payload and wrapped
that payload in another Result. The staged native ABI retained `Ok` while
losing the inner class handle. After successful freeze, the function now
returns the still-live original `registry` owner directly. The existing
alignment/identity behavioral spec now asserts that its unwrapped registry is
non-nil before reading it. A final cycle must rebuild Phase2 and repeat Stage3.

The final allowed cycle admitted ARM64 Phase2 SHA-256
`44165d7eb1dbe400050d17ab1f77641ca15cc8b2bbde0b66ff100aaa8a095a46`.
Stage3 again parsed and released all 665 surfaces, then exited 1 rather than
139 with the exact diagnostic:

```
Streaming module surface owner payload missing after phase 2
```

Thus the consumer hardening is accepted: the former HIR-entry SIGSEGV is now a
deterministic fail-closed error. Returning `Ok(registry)` one layer earlier was
insufficient; the outer `ModuleSurfaceBuilder.finish()` class-valued Result
still loses its payload.

No fourth cycle was started. The next correction must avoid returning the
owner through Result entirely: add a mutation API shaped like
`finish_into(existing_owner: ModuleSurfacesByName) -> text`, populate/freeze
the caller-created owner in place, and return only an empty/error text scalar.
The caller must retain and validate that same handle before wrapping it in
`Some`. Rebuild Phase2, require a non-nil unwrapped owner, then resume Stage3.
Kernel/QEMU rendering evidence remains unclaimed until that succeeds.
