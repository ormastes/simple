# Build11 Stage 3 CompileContext corruption after clean parse

## Status

The first fresh full-bootstrap repair attempt (`r4`) stopped during Stage 2 with
an inferred-`ANY` `ContractBlock.decrease_measure` diagnostic. Audit found a
partially present formal-verification slice: HIR consumers existed while the
flat-AST contract nodes and producer were absent. The coherent parser, AST, and
constructor slice is restored for the final source-frozen bootstrap attempt;
`r4` produced no Stage 2 admission verdict.

The final bounded `r5` attempt admitted Stage 2 (`858 compiled, 0 cached, 0
failed`; sanity `status=pass`, SHA-256
`d2ed1d54673bc4cc848024ebbc229a873053dc315d8412613184bfdc5faec947`).
Stage 3 still made no candidate: it held one core while RSS grew to about
19.8 GiB over 143 seconds, then was deliberately terminated before host OOM.
The wrapper recorded exit 143 and correctly refused Stage 4/seed fallback.
The session's three-cycle limit is exhausted; further localization is handed
off rather than retried here.

### Restart12 actor/process continuation

The detached actor/process lane resumed the admitted Stage-2 artifact against
the 616-file rebased closure. Cycle 1 completed HIR and found that commit
`19336b52905` had concatenated the
`fn defer_unsupported_marker(span: Span) -> Stmt:` header into its preceding
comment; restoring the declaration removed all six unresolved-name errors.
Cycle 2 received external SIGTERM 143 while four unrelated staged builders had
reduced host free memory below 2 GiB, so it yielded no compiler verdict. Cycle
3 ran after those builders exited, completed HIR, and reached MIR lowering, but
again emitted fourteen unnamed `cannot derive module constant type from folded
value` diagnostics. No candidate was produced and the three-cycle cap is
exhausted. A fresh lane must first make the Stage-2 diagnostic print the
constant name/span; another blind annotation sweep is not admitted.

The next actor/process recovery pass found that current main already owns the
actual fix: `mir_folded_const_type` classifies the original HIR expression
before matching the native payload enum. The retained admitted Stage 2 predates
that implementation, explaining why repeated Stage-3 runs could not consume
it. Three bounded attempts reduced a pure-Simple bootstrap-receipt planner from
four modules to one. The final stale-Stage-2 verdict rejected exactly the
planner's three explicitly typed module constants, confirming the old lowering
boundary rather than the constant owners. The prepared planner now has zero
module constants and no process runner; its next build is intentionally
deferred by the three-cycle cap. If it builds, use its typed receipt for a fresh
current-source Stage-2 transaction rather than resuming the obsolete authority.

Follow-up history audit found the allocation owner: `ModuleSurfacesByName` had
regressed from the reference-owned class established by `866559f16e0` to a
value struct. The post-store validation call consequently copied the complete
858-surface declaration graph before entering its scalar lookup. The class
invariant is restored with a source-contract regression; the admitted r5 Stage
2 remains the authority for the next cache-preserving Stage 3 resume.

The next bounded three-cycle audit disproved the post-store attribution. Making
the registry reference-owned and then inlining its scalar lookup did not change
the early RSS slope, and no HIR phase-profile sink was created. A third
trace-enabled run under GDB located the live stack in Phase 2 parsing:
`register_heap_ptr -> rt_enum_new -> convert_flat_stmt`, with 60 alternating
`convert_flat_stmt`/`convert_flat_stmt_in_list` frames below
`convert_decl_fn`. Build progress was between parse rows 128 and 192. The owner
is the 97-arm elif chain in
`src/compiler/70.backend/backend/common/ascii_utils.spl`, which the bridge
materializes recursively in the no-GC heap. It is replaced by the equivalent
`char_code` range check (printable ASCII plus tab/newline; `?` otherwise).
Verification of that final source change is deferred to the next session by the
three-cycle guard; Stage 3/4 remain BLOCKED, not failed by the unrun repair.

The subsequent three-cycle verification used a validated
`//bootstrap:stage3|reason=self-host-convergence-check` receipt. The first run
showed that removing the 97-arm ASCII chain alone did not clear parse progress
128. The second added a future bounded 120..200 per-file progress window, but
the admitted r5 executor necessarily retained its frozen 64-file cadence. The
third flattened the 41-arm `convert_flat_expr` dispatcher into semantically
equivalent early-return guards; it still stopped at parse progress 128 with
about 6.4 GiB RSS after 61 seconds. Inventory proves this is a systemic
recursive-if-chain cost: the admitted closure also contains chains of 52, 41,
37, 33, 31, 31, 28, and 19 arms. The next repair must make if/elif parsing and
FlatAstBridge conversion iterative/flat, then rebuild Stage 2 so the executor
itself carries that fix. More leaf rewrites are not accepted as completion.

Open. This blocks an admitted self-hosted compiler deployment and therefore
blocks the compiler/loader performance rows that reject Rust-seed evidence.
The historical `build/restart12-build11-a-r2/output` lineage is absent from the
current lane-B worktree, so its hashes cannot be reauthenticated or resumed
locally. The first r3 process was intentionally stopped before Stage 2 admission
so review corrections could be source-frozen. Its partial output is not
authority; it produced no Stage 2/3 verdict and consumes no acceptance/fix
cycle. The next source-frozen command rebuilds Stage 2 first.

## Reproduction

Historical lane-A evidence from a strict, provenance-recorded Build11 bootstrap
reported:

`Build complete: 845 compiled, 0 cached, 0 failed`

That admitted Stage 2 compiler then parsed all 603 Stage 3 closure files with
zero failures and exited 139 before the first HIR progress row. The fresh r3
lane's first source-frozen acceptance run produced an earlier Stage 2 verdict:
Rust authority compiled, then Stage 2 rejected `verification_contract_bridge.spl`
and `lean_backend.spl` because `proof_uses` was selected from `ANY`. Stage 3 and
Stage 4 were therefore not attempted by an admitted compiler.

The shared cause was an incomplete retained-contract HIR slice: MIR and Lean
consumers referenced `HirContractBlock`, while `hir_definitions.spl` lacked the
type, `HirFunction.verification_contract`, and constructor propagation. The
repair restores the type/field, initializes the currently unsupported parser
producer to `nil`, preserves the field through semantic resolution, and keeps
explicit unwrap typing at optional consumer boundaries. This is repair cycle 1;
the next source-frozen bootstrap was cycle 2. It admitted Stage 2 and entered
Stage 3, where MIR lowering rejected fourteen backend constants whose bare-zero
initializers could not safely determine a type. The constants are the complete
zero-valued CUDA/ELF/Mach-O/x86/AArch64 backend set in the Stage 3 closure; each
now carries the explicit `i64` type demanded by that fail-closed boundary.
The trace resume was retained but received an external SIGTERM before a
candidate and did not alter source. The canonical Stage 3 wrapper contains no
timeout around the native-build command, so no timeout owner or duration is
proved by that receipt.

Cycle 3 admitted Stage 2 again and removed all fourteen module-constant type
errors. Stage 3 then reached only source indices 0 through 2 before receiving
SIGTERM (exit 143). Its retained log is 883 bytes and contains no compiler
diagnostic or admitted candidate.

A fresh long-lived resume removed the external command-duration ambiguity. The
admitted Stage 2 process remained runnable at about 100% CPU, but after source
index 2 `post-store` its RSS grew from about 7.4 GiB to 20 GiB in four minutes
without further log or I/O progress. It was terminated before host OOM. The
exact interval is module-surface lookup: the old linear search passed each
large `ModuleSurface` aggregate by value before rejecting a mismatched scalar
source index. The repair first resolves through the registry's native-safe
scalar name/index arrays, validates one candidate by physical identity, and
retains a scalar-prefiltered fallback for compatibility spellings.

## Evidence

GDB resolves the crash to:

`CompileContext.error_count -> CompilerDriver.lower_and_check_impl -> CompilerDriver.compile`

The historical lane-A Stage 3 log was empty and the diagnostic immediately
after the first `self.ctx.error_count()` call never printed. In that lane,
replacing getter calls in the driver with direct `error_count_value` reads did
not change the terminal result, so that unproven workaround was removed. This does not
invalidate the earlier `3c26d1b9c2f` observation that direct scalar reads
advanced a different Stage3 run into HIR; the historical lane-A failure
frontier was earlier. The fresh r3 frontier is unknown until the corrected run
exits and its manifests verify.

An earlier parser blocker in
`compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` was independently
fixed with required parentheses around a multiline boolean. Both subsequent
cycles parsed all 603 files, so this context corruption is the remaining
blocker.

## Historical unblock condition (superseded)

The former receipt-less command was:

`env BOOTSTRAP_NATIVE_CACHE_TTL_DAYS=0 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy --backend=cranelift --output=build/restart12-build11-a-r3/output`

Do not run it as written. Current policy requires the planner-produced receipt
described below. After that prerequisite is repaired, do not set
`--fresh-cache`: the Rust seed may build Stage 2 only; admitted Stage 2 must
build Stage 3, and admitted Stage 3 must build Stage 4.

Retain the Stage2/Stage3/Stage4 build logs, command transcripts, sanity/provenance
manifests, candidate hashes, and the focused GDB backtrace. Add fixed-string,
context-free
canaries at `lower_and_check_impl` entry, after the `source_path_map` loop, and
immediately before/after `module_surfaces_from_modules`; if corruption crosses
that call, capture its MIR/native IR and add an adjacent aggregate-return/copy
regression. Do not retry getter-only edits without new localization evidence.

Current localization surfaces are four fixed-string `dtrace` canaries in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`: entry, after the
source-path map, and immediately before/after module-surface extraction. The
adjacent deterministic boundary probe is
`test/02_integration/compiler/stage3_context_tuple_return_native_probe.spl`;
it returns `(Context, bool)`, reinstalls the context, and checks both direct
scalar and trivial-getter reads. Neither is acceptance evidence until executed
by an admitted native compiler with `SIMPLE_NO_STUB_FALLBACK=1`.

Produce one admitted Stage 3 candidate that passes provenance and frontend
sanity, deploy the full pure-Simple CLI, then run the focused loader SPipe gate,
C provider self-check, optimizer audit, and retained failed-probe/latency/RSS
measurement exactly once.

## Bounded lane-A localization result

Three recovery cycles were consumed without producing an admitted candidate.
The first reproduced exit 139. The second enabled `SIMPLE_INTERP_TRACE=1`, but
the provenance wrapper intentionally reconstructs the Stage 3 environment and
did not admit that variable. The final cycle used unconditional primitive-only
entry, post-source-map, pre-surface, and post-surface canaries in
`lower_and_check_impl`; Stage 3 again exited 139 and its retained native-build
log remained empty. The diagnostic canaries were removed after the run.

This result does **not** prove that `module_surfaces_from_modules` is the active
frontier: no `lower_and_check_impl` entry canary was observed. Resume work must
first establish whether control reaches that method under a trace-preserving
provenance command or debugger breakpoint, then inspect the aggregate call only
if the entry/source-map canaries execute. The three-cycle cap is exhausted for
this lane; do not repeat the same recovery command without a new instrumented
or debugger-backed localization strategy.

## Bootstrap-receipt planner prerequisite

Current bootstrap policy requires a planner-produced authorization receipt.
The available release ELF (SHA-256 prefix `04a38e...`) exits 139 before planner
entry. GDB localized the failure to `handle_build+703`: C `rt_cli_get_args`
creates argv in the hosted runtime's private array registry, selected
pure-Simple `rt_slice(args[1:])` rejects that owner and returns nil sentinel
`3`, and the caller dereferences it.

A selected-owner bridge prototype proved atomic hook selection, exact argv
content, empty/failure handling, and whole-archive symbol retention. Final
review rejected it because its strong bridge bodies still called duplicate
global `rt_array_new`/`rt_array_push` symbols. Under
`--whole-archive --allow-multiple-definition`, those relocations can bind back
to the C owner, while the archive test was not registry-discriminating. The
prototype was removed after the third bounded fix cycle.

The next fresh session must factor private, non-interposable pure-Simple
allocation/push helpers, make the selected-owner bridge call only those
helpers, and prove argv with a registry-sensitive pure-owner operation under
the production whole-archive link policy. Non-GNU mixed-owner linkage remains
a platform WARN. Only after a rebuilt CLI emits the mandatory receipt may a
new source-frozen Stage-3 diagnostic run begin.

### Historical private-owner follow-up result (superseded below)

A fresh three-cycle session implemented the private-helper shape and exercised
it under the production GNU whole-archive/multiple-definition policy. The
deliberate-red archive correctly reached poisoned public array providers before
the fix. After the fix, an empty argv plus direct private allocation/push was
registry-valid, proving the private ownership path itself.

Populated argv still failed: Stage 2 lowered both the fail-closed
`push_owned(...) < 1` and `push_owned(...) == 0` conditions to an indirect
`rt_native_eq` call, but the pure runtime archive did not define that symbol.
The final executable therefore segfaulted at the unresolved GOT call after a
successful private push. The fresh archive built all 18 parts with zero
failures, so this is a runtime-closure/link defect rather than a parse/build
failure. The prototype and tests were removed at the cycle cap.

Next work must add and prove `rt_native_eq` in the actual pure runtime closure
(or another fail-closed comparison primitive already admitted by that closure),
then reapply the private-owner bridge and rerun the populated, registry-sensitive
whole-archive test. Silently ignoring the push result is not an acceptable
shortcut.

### Argv closure proved; planner link moves forward

The next fresh session proved the apparent equality gap was linker retention:
the archive already contained one strong `rt_native_eq`, but the permissive
diagnostic link discarded its provider and zero-filled an unresolved GOT slot.
The corrected ELF regression uses `-z defs`, explicitly roots
`rt_native_eq`, and retains the whole pure archive. It proves one defined
provider, no unresolved/dynamic equality relocation, populated
`simple/build/bootstrap` strings, a pure registry-owned argv array, and zero
calls to poisoned public `rt_array_new`/`rt_array_push` providers.

The accepted implementation gives the pure owner private, non-interposable
argv allocation/push helpers and makes the competing hosted C argv group weak.
Pure `spl_arg_count`, `spl_get_arg`, `rt_get_argc`, count/at, and all array
aliases share one state. A fresh archive built all 18 parts with zero failures
and the expanded regression passed. macOS/Windows behavior remains WARN.

A bounded current-planner build then advanced through all 856 closure files.
Cycle 1 fixed one Stage-2-parser-incompatible mixed inline/multiline conditional
without changing semantics. Cycle 2 timed out at 600 seconds and retained 370
cached artifacts. Cycle 3 resumed that cache with two threads, compiled the
full closure, and failed only at link: four references from
`convert_nodes.spl` target `defer_unsupported_marker`, but no definition exists
anywhere in the source tree. No planner binary or receipt was produced.

Inspection traced the missing symbol to commit `19336b529055`, which appended
the function signature to the preceding comment and left the body orphaned.
The exact `fn defer_unsupported_marker(span: Span) -> Stmt:` header is restored.
Because the three planner-build cycles were already exhausted, that final
repair is source-reviewed but not link-verified. The next fresh session must
add/run a focused closure/link guard and rebuild from the retained 856-entry
cache. Only after the planner emits the mandatory receipt may Stage 3 start.

### Restored-header follow-up: runtime-authority incompatibility

The next bounded session advanced past the former four-reference failure.
Cycle 1 populated a refreshed cache but timed out without a compiler error.
Cycle 2 reached link and exposed three missing real providers in the retained
Rust bootstrap authority: `rt_mem_snapshot_open`, `rt_mem_snapshot_record`,
and `rt_mem_snapshot_close`. The Rust bootstrap runtime now implements the same
snapshot contract as `runtime.c` on Linux; its focused create/write/exclusive-open test
passes, and an isolated bootstrap archive exports all three symbols.

Cycle 3 used that archive and advanced to a single link failure: the retained
r2 Stage-2 compiler lowered current `write_elf_bytes_to_file` to
`rt_array_data_ptr_u8`. That unsafe ABI was intentionally removed, so restoring
it as a stub or compatibility escape is forbidden. No planner executable or
receipt was produced, and Stage 3 did not start. The three-cycle cap is
exhausted.

Next action is a fresh coherent-authority build: compiler lowering, runtime
archive, and sources must share one revision. Prove the planner link has the
three snapshot definitions and zero undefined old-pointer ABI, then emit the
typed `//bootstrap:stage3` receipt. Because the normal wrapper continues into
excluded Stage 4 and admitted resume cannot rebuild current Stage 2, add and
review a fail-closed `--stop-after-stage3` route (or equivalent) first.
