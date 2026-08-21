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

## 2026-08-22 planner admission link regression

The next fresh-cycle admission producer failed before authorization with
`Undefined symbols for architecture arm64: _file_delete`. The minimal planner
documents a bounded bootstrap-recovery ABI for delete/write, but imported
`file_delete` through `std.io_runtime`; the admitted Phase-2 compiler emitted
the facade name rather than the core-C runtime export `rt_file_delete`.

This planner is the explicit bootstrap recovery boundary, so the smallest
owner fix is to declare and call `rt_file_delete` beside its existing
`rt_file_write_text_at`. Acceptance requires the producer self-test and a real
source-bound Stage-3 admission receipt. No general app/runtime shortcut is
introduced.

The first `finish_into` bootstrap cycle admitted Phase 2 at SHA-256
`ad3060d54edfb67a66901cfa3d121ecb861fcbc348f97cceb34446a03cc7757d`.
Stage 3 parsed and released all 665 surfaces, then failed closed with
`Module surface alignment error: module surface destination is not empty`.
The remaining hop was `ModuleSurfacesByName.empty()`, itself a class-valued
return. Cycle 2 constructs the destination directly in the driver frame before
passing it to `finish_into`; no class-valued return may create or transfer the
streaming owner.

Cycle 2 admitted Phase 2 at SHA-256
`44386d4864eebf00985dfecc271579c694decaa0a0cd2d8665a152a7def00f2d` but
reported the same destination error after 665 releases. Therefore the direct
constructor was not the remaining transfer; the staged compiler misread the
pre-population compound emptiness predicate. `finish_into` now implements its
literal mutation contract: after nil/frozen-builder guards it validates the
builder data and overwrites the destination fields. The adjacent regression
uses a successful first finish, then proves a second finish is rejected before
mutating a sentinel destination.

Cycle 3 admitted Phase 2 at SHA-256
`30f2e469df42a696f41a82a97234c2e287b277d28302d1e82ee1638152078401`.
Stage 3 crossed the former owner guard, entered `phase3:hir_typecheck:start`,
and began lowering the retained 665-surface inventory. This proves the
caller-owned `finish_into` transfer itself is live. The first imported module
immediately failed lookup, however, and the run accumulated broad
`missing module surface` diagnostics before a later SIGSEGV at source index 98.

The retained registry lookup contradicts its own scalar-index design comment:
`module_surface_registry_index` still reads only `registry.index_by_name`, even
though `ordered_names`/`ordered_indices` are the native-safe authoritative
representation and the compatibility dictionary is documented as
construction-time-only. The next fresh cycle must make the registry lookup scan
the aligned ordered arrays, add exact hit/miss plus adjacent alias tests through
the registry API, and only then rebuild. No fourth cycle was started. Stage 3,
the ARM64 image, and QEMU rendering evidence remain unclaimed.

Fresh-turn source review refined that handoff before implementation. An ordered
scan would restore correctness but regress every import lookup from O(1) to
O(module-count). Freeze validation proves the builder dictionary is complete;
the loss happens because `finish_into` replaces the caller-owned dictionary
with the value-struct builder's dictionary and that storage expires after the
method returns. The implemented fix retains the destination dictionary object
and fills it in place from the aligned ordered arrays. Exact name, adjacent
alias, and miss regressions read through the retained dictionary after return.

The first retained-index cycle admitted Phase 2 at SHA-256
`7caf97ba784f18084227058a015ce8469b78d8333a5f60780d7194178a35bf38`.
Stage 3 still lost every imported lookup from the first dependent module. This
proves indexed assignment through the `registry` class-valued parameter mutates
a temporary Dict field value. Cycle 2 moves that mutation onto a
`ModuleSurfacesByName` mutable receiver and checks each inserted name/index
immediately; a failed retained write now returns a scalar alignment diagnostic
before HIR instead of permitting a missing-import cascade.

Cycle 2 admitted Phase 2 at SHA-256
`15a5762c72684001d83f67dcb5dc74dfab7f4fa8d332906dc4f5916ed5ddbea7`.
The per-write receiver check succeeded during freeze, yet post-return HIR again
lost imported names from the first dependent module. The nested Dict therefore
cannot be authoritative after the builder frame ends. Cycle 3 switches the
post-freeze `module_surface_registry_index` to the retained aligned scalar
arrays with malformed-alignment/index rejection and direct exact/alias/miss
coverage. Export-origin fixpoint lookup remains on its live construction Dict;
only bounded HIR module-name lookup uses the scalar scan.

Cycle 3 admitted Phase 2 at SHA-256
`28dd6579acbdfe5eebfd9618687ee9d39d9de50940d24b68017628d8bf613031`.
The scalar arrays were also empty after `finish_into` returned, so lookup still
failed from the first dependent module and later segfaulted. Both current-turn
lookup experiments were removed: neither fixed the owner lifetime, and the
linear scan would have added a performance regression.

Runtime/source tracing identifies the actual missing ownership transition.
Each individual `ModuleSurface` is deeply promoted while its per-file transient
scope is paused, explaining why `surfaces` remains iterable. The final registry
class and its Dict/text-array graph are created after those scopes end and are
never passed to `rt_transient_heap_promote`. That runtime API explicitly walks
raw/class aggregates and all reachable arrays and dictionaries. The next fresh
cycle must create the completed registry inside a dedicated transient retention
scope, pause it, deeply promote the registry graph through a module-surface
owner facade, end the scope, and only then commit the Option to the driver.
Exact and adjacent tests must prove post-scope name, alias, miss, and malformed
index behavior. Stage 3, ARM64 image, and QEMU remain unclaimed.

The first registry-promotion cycle admitted Phase 2 at SHA-256
`d32fc781caaddb4706c2d5f519edb662a0678027497dc5fbc995fa628e6e7ab6`.
Deep promotion returned success, but Stage 3 still reported missing imported
surfaces from the first dependent module and later segfaulted. Cycle 2 adds a
post-scope `module_surfaces_frozen_alignment` gate before driver commit. It
checks the complete frozen registry invariant and reports retained surface,
name, index, and Dict counts on failure, so HIR cannot consume a partially
retained graph.

Cycle 2 admitted Phase 2 at SHA-256
`7054048f76a927c76d7ebaf800688de362b91e152d6ff8f7695367325d44a1f7` and
failed cleanly before HIR with exact retained counts:
`surfaces=665 names=943 indices=943 dict=-1`. Deep promotion therefore retains
the complete class and scalar arrays; only the Dict carrier is invalid after
scope teardown. Cycle 3 rebuilds that compatibility Dict directly from the
retained arrays after the transient scope has ended, then requires the full
frozen-alignment invariant before committing the registry.

Cycle 3 admitted Phase 2 at SHA-256
`3dc08dd7fd7157d7cb69b69774553ef518b9ac873fa20e1cfe1e95194494b61b` and
reported the identical clean pre-HIR state. Rebuilding a Dict after teardown
was ineffective because assigning any Dict carrier into the registry class
field is lost on this staged path; that attempted rebuild was removed.

The retained evidence now supports one combined correction: keep the deep
promotion that preserves all 665 surfaces and 943 aligned scalar entries;
make post-retention name lookup and retained-alignment validation use those
scalar arrays; and treat `index_by_name` as construction/freeze-only. The prior
scalar-only experiment ran before the registry graph was promoted, so its text
elements were not retained; repeating it on the promoted graph is a distinct
root-cause fix, not a retry. No fourth cycle was started. Stage 3, ARM64 image,
and QEMU remain unclaimed.

The next fresh cycle implements that combined correction without slowing the
construction path: `module_surface_registry_index` uses the compatibility Dict
when `len() >= 0`, and otherwise scans the deeply promoted aligned arrays. The
existing full frozen-alignment check then becomes a post-retention scalar
invariant automatically, while exact name, alias, miss, and malformed-index
coverage remain bound to the same public registry lookup.

## Stage-2 trust-root refresh blocker (2026-08-22)

The first post-fallback bootstrap attempt used the older admitted Phase-2
parent and failed while lowering `src/lib/nogc_sync_mut/io/file_ops.spl` with
an undeclared `ffi` global. A direct probe distinguishes that symptom from the
source contract: the retained admitted compiler crashes during parse, while a
newer unreceipted compiler parses the same six-module closure and crashes only
after entering HIR. The FFI annotations must therefore remain intact.

The canonical `--full-bootstrap --stop-after-stage2` trust-root refresh then
stopped before producing a compiler: Rust LLVM lowering destructured
`MirInst::ClosureCreate` without its newly added `return_type` field
(`E0027`, `compiler/src/codegen/llvm/functions.rs:1072`). Sibling dispatch and
instruction lowerers already ignore that metadata explicitly. The bootstrap
fix is to make the LLVM pattern equally exhaustive; `cargo check` is the exact
regression because this mismatch cannot compile, and the sibling closure
lowerers are the adjacent consistency evidence.

The exhaustive-pattern correction passed `cargo check -p simple-compiler`.
The third and final bootstrap cycle then completed the canonical Stage-2
trust-root refresh and admitted a pure-Simple compiler at SHA-256
`913990d1192ade4ca1828714619b0f7ae78dccbf52f774ddb912953757fd25a3`.
Its `stage2-provenance.receipt` reports
`authority=explicit-full-bootstrap-stage2-trust-root`, and its independently
bound `stage2-sanity.receipt` reports `stage2-sanity: pass`; both bind the same
candidate and admission receipt. The earlier undeclared-`ffi` symptom did not
recur. The mandatory three-cycle cap stops this session before Stage 3. The
admitted Stage-2 artifact is the exact next-session parent; Stage 3, the ARM64
image, and all real-QEMU rendering surfaces remain unclaimed.

## Retained export-origin index diagnosis (2026-08-22)

The next canonical Stage-3 cycle rebuilt and admitted its Stage-2 capsule, then
failed cleanly after parsing and individually promoting all 665 surfaces. The
post-retention diagnostic again reported `surfaces=665 names=943 indices=943
dict=-1`. Inspection shows the top-level name lookup already has its scalar
fallback, but `module_surface_route_arrays_aligned` still calls
`export_origin_index.origins.contains_key` for every retained surface, and
`module_surface_export_origin_index_lookup` still depends exclusively on its
nested `index_by_name` Dict. Those nested compatibility Dicts share the same
transient-carrier failure mode even though their aligned name/owner/source/kind
arrays survive.

The owner fix is to give export-origin lookup the same construction-fast,
retention-safe policy: use the Dict while valid, otherwise scan the aligned
scalar names; validate the selected position against every scalar payload
array; and make retained route validation exercise that public scalar-aware
position lookup. Exact regression evidence adds a non-empty export-origin
entry to the existing promote/end-scope registry test and proves hit, miss,
and retained alignment after teardown. Misaligned payload arrays remain a
fail-closed adjacent case.

Cycle 2 retained the same aggregate failure, so cycle 3 added a first-failing
invariant diagnostic instead of guessing. The final permitted run identified
surface 0 precisely: `imports=6`, while its post-freeze route arrays reported
garbage lengths from `5863548` through `5875862`; its pre-freeze export-origin
scalar arrays all remained length 0. This proves the remaining lifetime split.
Each `ModuleSurface` raw object is promoted during its per-file scope, but
freeze attaches newly allocated import/export route arrays later, inside the
registry retention scope. Promoting the registry cannot traverse through an
already-promoted raw surface allocation, so those new children are reclaimed.

The queued owner correction explicitly promotes every post-freeze route array
while the registry scope is paused, before promoting the registry carrier and
ending the scope. This source correction is intentionally left unclaimed in
this session: the mandatory third-cycle stop was reached. The next cycle must
rebuild Phase 2 and require the detailed retained-alignment diagnostic to be
empty before Stage 3 may proceed.

The next Stage-3 cycle cleared that retained-alignment gate and entered HIR,
proving the explicit route-payload promotion. HIR then failed from source 1
with `missing module surface` for almost every import and eventually exited
139. The first failing path still queried
`self.module_surfaces.index_by_name.contains_key(...)` directly in six import
resolution/key-normalization branches. That Dict is intentionally invalid
after retention (`len() == -1`), so it can report a spurious hit; the subsequent
scalar-built `surface_index_for_name` correctly returns `-1`, producing the
observed contradiction.

All retained HIR membership decisions must use `surface_index_for_name`, whose
per-lowerer Dict is rebuilt from the promoted ordered name/index arrays. The
construction/freeze owner remains the only code allowed to access the original
compatibility Dict directly.

Cycle 2 removed all `missing module surface` failures, but imported types and
functions remained unresolved from source 1. The retained module identities
and routes are therefore sound; the next layer is each surface's declaration
payload. `register_imported_symbol` reads `composites`, `enums`, `traits`,
`callables`, and `constants`, while the existing per-file promotion relies on
walking through the `ModuleSurface` raw class carrier. The route-array result
already proved that raw-carrier traversal is not a sufficient ownership
boundary.

The per-file promotion facade now promotes every declaration name array,
declaration Dict, import/export array, impl array, and export-origin index
carrier explicitly before promoting the surface class. Retained alignment
also requires each declaration Dict length to equal its scalar name projection,
so Stage 3 fails before HIR with exact counts if any declaration carrier is
lost.

Cycle 3 proved that direct promotion is not a viable Dict transport: surface 0
retained `callable_names=26`, but `callables.len()=-1`; every other declaration
Dict also reported `-1` while its scalar name array remained valid. The new
alignment gate therefore failed cleanly before HIR rather than repeating the
unresolved-symbol cascade. No fourth cycle was started.

The required next owner change is structural, not another promotion retry.
`ModuleSurface` needs aligned value arrays beside `composite_names`,
`enum_names`, `trait_names`, `callable_names`, `type_alias_names`, and
`constant_names`. Construction may retain Dicts as fast mutable builders, but
freeze must publish name/value arrays and all post-retention declaration
membership and payload reads must use those arrays. This follows the existing
route-array rule already documented on the class: no
`Dict<text, aggregate>` crosses the native Stage-3 boundary.

## Retained declaration payload Cycle 1 (2026-08-22)

Commit `4576fa621848` published index-aligned declaration value arrays and
migrated retained HIR lookups away from construction dictionaries. The first
fresh admitted Stage-3 cycle cleared the previous declaration-length gate and
entered HIR, but the first imported source (`compiler.driver.driver`) lost
`CompileOptions`, `CompilerDriver`, and `CompileResult`. The failure broadened
into unresolved imported declarations and ended with signal 11 at source 68.

Array survival alone therefore does not prove aggregate payload survival. The
next bounded cycle adds a pre-HIR invariant that compares every retained value
payload's `name` with its aligned scalar name. It fails closed at the first
corrupt aggregate, before imported-symbol lowering can cascade or crash. Only
if names remain aligned may diagnosis move inward to nested type/parameter
payload retention.

Cycle 2 proved every retained aggregate `name` still matched its scalar key,
yet reproduced the same source-1 unresolved-import cascade. The remaining
retained read was earlier: `resolve_import_symbols` iterated each nested
`ParserImport.items` array after per-file teardown. An invalid negative nested
length makes both the glob and explicit-item branches perform no registration,
which exactly explains why module routing succeeds while all named imports are
missing.

The owner fix publishes import-item offsets, names, aliases, and alias flags as
flat scalar arrays on `ModuleSurface`. HIR now checks the aligned offsets and
unwraps item positions only inside their validated range. The nested-glob path
uses the same projection, so it cannot reintroduce the stale parser payload.
Cycle 3 is the final permitted bootstrap verification cycle for this session.

Cycle 3 rebuilt and passed Stage-2 sanity, then failed immediately after
parsing the first Stage-3 source with SIGBUS (exit 138). The new projection had
read `ImportItem.alias` unconditionally. Although desugared as `text`, the
parser stores `nil` when `has_alias` is false; consuming that field before the
presence check reproduces the struct/optional ABI hazard at surface creation.
The queued correction unwraps `alias` only when `has_alias` is true and stores
an empty scalar otherwise. It is intentionally unclaimed until a fresh scoped
session runs the next admitted Stage-3 cycle.

## Flattened import-item Cycle 1 (2026-08-22)

The fresh admitted cycle proved the nullable-alias guard: the first surface
completed construction, promotion, commit, and release. The next surface
(`compiler.driver.driver`) parsed, then crashed during surface construction.
Inspection found the projection loop incorrectly reading `source.imports` from
`SourceFile`, whose authoritative fields are only path/content/module metadata.
Parsed imports belong to `owner.value.imports`. This invalid structural field
read explains the file-dependent SIGSEGV and must be corrected at the owner
boundary before Cycle 2.

Cycle 2 completed all surface construction and entered HIR, then failed
cleanly because every importer lookup used raw `src/.../*.spl` paths against a
registry keyed by dotted logical module names. The existing relative-import
path already defines the correct canonicalization: remove `.spl`, replace `/`
with `.`, and remove the leading `src.`. The importer surface must be resolved
with that canonical key before its validated flat import-item ranges are read.

Cycle 3 proved the canonical key for the entry module, then every later module
again reported a missing importer surface. The one-time per-lowerer
`surface_index_by_name` cache is a transient Dict: it works for source 0 but
false-negatives after that module's scope transition. The registry's promoted
ordered name/index arrays remain authoritative. `surface_index_for_name` must
therefore treat a cache miss as inconclusive and fall back to
`module_surface_registry_index`, which already scans those retained scalar
arrays when the construction Dict is unavailable. The three-cycle cap prevents
claiming this queued correction until the next fresh session.

## Scalar registry fallback Cycle 1 (2026-08-22)

The fresh cycle removed every `missing importing module surface` diagnostic
and advanced HIR from source 1 to source 71. Imported composite registration
then produced bogus dependencies such as `Type`, `Expr`, and `Block`. The
field array and its scalar projections survived; the defect is that composite
dependency discovery always traversed the retained parser `Type` enum instead
of preferring `ModuleSurfaceField.type_name` and `array_element_name` as the
callable path already does. Native scalar projections must be authoritative
for simple named and array fields, with parser-Type traversal reserved only for
unprojected compound shapes.

Cycle 2 regressed nondeterministically: `CompileOptions` itself was again
unresolved and the crash moved from source 71 to source 61. A fallback only on
cache miss is therefore insufficient; the transient Dict can also report a
spurious hit or wrong retained index. Retained HIR lookup must bypass the
per-lowerer Dict entirely and call `module_surface_registry_index`, whose
construction Dict is rejected when invalid and whose ordered scalar arrays are
the authority. This reintroduces linear lookup cost and is a recorded
performance follow-up; correctness and Stage-3 admission take precedence over
an untrustworthy O(1) cache.

Cycle 3 stabilized cache-independent routing but still lost facade declarations
such as `CompileOptions`, `BootLogger`, and `SourceFile`. Inventory found three
remaining retained HIR traversals in `module_reexport_materialization.spl`
reading nested `ParserImport.items` directly: facade chase, enum payload
explicit imports, and callable dependency explicit imports. Those stale arrays
bypass the flattened projection and explain why direct modules resolve while
facade exports do not. All three must consume the validated offset/name/alias
scalar arrays. This correction is queued after the three-cycle cap and remains
unclaimed until a fresh admitted run.

Diagnostic Cycle 2 captured the same `(facade, wanted)` query returning
`found=true` during early lowering and `found=false` after module-scope
transitions. The scalar route walk is correct; the cross-module root memo
arrays are not retained authority. Re-export resolution must start with fresh
visit arrays per root query and return the live scalar-route result without
reading or publishing the transient root memo. This is another deliberate
performance rollback until a retention-safe index exists.

Cycle 3 showed that removing the memo does not restore facade matches. Combined
with Cycle 2 diagnostics, the same import items are readable during early
surface work but absent after the freeze/module transition. Their projections
were constructed in the per-file surface scope, unlike the proven import target
and export route arrays constructed in the registry freeze scope. The owner fix
is to build flat import-item offsets/names/aliases during freeze, attach them
beside the target routes, and explicitly promote them in
`module_surfaces_promote`. Per-file construction is not an ownership boundary.

## Freeze-owned import-item Cycle 1 (2026-08-22)

The fresh admitted run rebuilt Stage 2 and passed its compiler sanity and
struct-receiver/runtime capability gates. Stage 3 entered HIR, but the original
facade declarations (`CompileOptions`, `BootLogger`, and `SourceFile`) were
again unresolved from source 1 and the process exited 139 at source 31.

The freeze-owned implementation still traversed `ParserImport.items` while
freezing. That nested parser array already belongs to the ended per-file scope;
moving the traversal later therefore moved the stale read instead of removing
it. The corrected ownership handoff flattens items while each parser payload is
alive, explicitly retains those scalar arrays to freeze, validates their
offsets, then clones them into fresh registry-scope arrays. Freeze never reads
`ParserImport.items`, and the registry promotion retains only the fresh clones.
Nullable aliases remain read only after `has_alias` is true.

Cycle 2 passed the new pre-freeze offset/range gate but reproduced the same
source-1 facade failures and exited 139. Cycle 3 enabled the existing import
diagnostics. They proved `driver.spl` retained all 19 imports, including three
items from `compiler.common.driver_core_types`; that re-export route returned
`found=true` while lowering source 0, then `found=false` for the identical
`CompileOptions` query while lowering source 1. The item projection correction
is therefore sound, but it exposed the next lifetime boundary.

`find_reexport_source_walk` tests the target through aligned declaration name
arrays. Those arrays and their value peers are still allocated in per-file
scopes. Explicit promotion carries them to freeze, but does not republish them
under the registry scope that survives successive HIR module teardowns. The
queued correction shallow-copies every declaration name/value array during
freeze and explicitly promotes those new registry-scope carriers. This is left
unclaimed because Cycle 3 exhausted the session cap; the next fresh session
must prove that the identical query remains `found=true` after source 0.

## Freeze-owned declaration Cycle 1 (2026-08-22)

The fresh admitted run rebuilt Stage 2 in approximately six minutes and passed
compiler sanity plus struct-receiver/runtime capability. Stage 3 still exited
139. The identical `driver_core_types -> CompileOptions` query was false at
source 1, true again during later modules, and false again after that. A single
declaration-array teardown cannot explain this reversible result. Cycle 2 adds
a diagnostic-only record at each matching re-export hop with its retained item
range, selected target index/name, declaration decision, and all declaration
name-array lengths. No semantic change is made until that record identifies
whether route selection or the target declaration carrier is unstable.

Cycle 2 proved both are stable. Every successful `CompileOptions` hop selected
target 25 (`compiler.common.driver_compile_options`), retained item range
10..14, and reported `declares=true`, `composites=1`. Failed root queries
emitted no hop record at all, so they returned before scanning routes. The
shared `HirLowering.reexport_visit_*` arrays are reset by assigning fresh local
arrays, but nested root queries and native cross-module return synchronization
can restore an older field snapshot containing the same root at depth zero;
cycle detection then rejects a new root as already visited.

Cycle 3 replaces that shared recursion state with a fresh explicit
`HirReexportWalkState` carrier passed through recursive calls. Nested root
queries receive different carriers, so they cannot overwrite or resurrect the
outer root's visited set. Compatibility completion/valid flags are copied back
only after the walk returns.

Cycle 3 still reproduced the source-1 false result, so the three-cycle cap was
reached. Failed calls continued to emit no hop, proving the return remains in
the pre-walk root validation. That validation accepts a by-value
`ModuleSurface` aggregate, extracts its index, then compares several aggregate
fields with the registry copy. This is the final aggregate ABI boundary on the
route. The queued owner correction changes the root API to accept only the
scalar physical index and wanted name, then loads and validates the canonical
surface from the retained registry. It remains unclaimed until a fresh session.

## Scalar re-export root Cycle 1 (2026-08-22)

The fresh admitted run rebuilt Stage 2, passed compiler sanity and the
struct-receiver/runtime capability gate, then reproduced the same source-1
unresolved facade cascade and exited 139. Failed queries still emitted no hop,
so passing the scalar extracted at the caller was insufficient. Cycle 2 labels
every remaining pre-walk return independently: registry alignment, legacy memo
alignment, scalar index bounds, canonical physical-index equality, and
generation equality. This preserves fail-fast diagnosis without weakening any
registry invariant.

Cycle 2 identified the exact pre-walk rejection: `reason=memo-misaligned` for
every failed query, including source-1 `CompileOptions`. Root memo reads and
writes had already been disabled because those arrays are not retained
authority, but generation reset and the legacy alignment guard remained. After
the first lowering transition their transient fields diverged and the obsolete
guard rejected every live scalar-route query. Cycle 3 removes root-memo
clearing and alignment validation entirely. Registry alignment, scalar physical
identity, generation, per-root cycle state, and live route traversal remain
fail-closed and authoritative.

## Scalar re-export root Cycle 3 (2026-08-22)

The admitted run again rebuilt Stage 2 and passed compiler sanity plus the
struct-receiver/runtime capability gate. Removing the obsolete memo gate moved
Stage 3 HIR from the prior source-1 facade failure through source 178 of 666.
The process then exited 139 while lowering the return type of
`detect_llvm_capabilities` in
`src/compiler/backend/backend/llvm_capability.spl`. The log also records an
accumulating unresolved-type/name cascade before that crash, including the
first local export-index failures at source 177. This is real forward progress,
but not a trusted Stage 3 compiler. The session's three-cycle verification cap
is exhausted; the next owner fix and rerun must start in a fresh session before
ARM64 or QEMU evidence can be claimed.

## Scalar import materialization cycles (2026-08-22)

A fresh three-cycle admitted session extended the scalar physical-index
boundary through all imported-symbol registration call sites. Each cycle's
Stage 2 passed compiler sanity and the struct-receiver/runtime capability gate;
each Stage 3 remained strict (`SIMPLE_NO_STUB_FALLBACK=1`) and exited 139 in
HIR. Cycle 1 reached 81/666 modules, Cycle 2 reached 74/666, and Cycle 3 reached
56/666. All three retained the same first fatal family at source 1:
`HirImpl`, `HirStaticAssert`, `HirAopAdvice`, `HirDiBinding`, `HirArchRule`, and
`HirMockDecl` unresolved while lowering `driver.spl`. Therefore the differing
crash endpoints are downstream/non-deterministic and do not prove progress.

The session also replaced direct `lookup(...).?` presence checks in import
registration with `lookup_or_invalid(...).is_valid()` and made same-owner
composite revisits close dependencies instead of returning early. Neither
removed the source-1 family. The retained trace establishes the remaining
semantic gap: a chase from facade `compiler.hir.hir_types` finds declarations
in terminal `compiler.hir.hir_definitions`; registration binds only the terminal
qualified identity, then field projection immediately queries the facade-
qualified identity and reports it unresolved. A queued owner fix now publishes
the successfully registered terminal type under the facade-qualified alias in
the re-export branch. It is intentionally unclaimed until a fresh admitted
session; the three-cycle cap forbids another run here. ARM64 and QEMU remain
pending on a trusted Stage 3.
