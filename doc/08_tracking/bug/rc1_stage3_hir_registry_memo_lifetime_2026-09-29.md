# RC1 Stage 3: frozen-registry memo lifetime

Base: release/1.0 `42ea10e42a899f1dc58d60e76c8de076add0ede3`.

## Failure

Stage 3 intermittently stalls in imported impl registration with unbounded
allocation, or reaches a later block-tail payload-copy crash. The former is
confirmed to read reclaimed cache storage; the latter needs renewed evidence
after repairing ownership.

LLDB on the previously admitted macOS Stage 2 binary, with ASLR disabled and
10 workers configured, stopped in `register_imported_type_methods_inner`.
The saved outer impl cursor was `0x313f6` (201718). The retained positions
array at `0xa6f9925a0` contained words `0x13, 0x108d98931, ...`, rather than
an array header and bounded length. The inner method-key array was valid and
had length 40. Thus the outer loop compared its cursor with a reclaimed
array's pointer-valued length. The process was explicitly killed after capture.

Evidence: `build/native_probe/config-layout/outer-loop-current.log`.
Earlier diagnostic: `hir-bound-current.log` reached HIR 24/717 and faulted
in `lower_hir_block+2060` at address `0xd38`; no bootstrap PASS is implied.

## Ownership repair

`begin_module` deliberately retains registry-pure caches. Their roots can
predate the per-module transient scope, while their keys and array rows are
allocated inside it. The streaming driver promoted diagnostics and HIR but
not these retained memo graphs before ending the scope.

Add `HirLowering.promote_registry_memos_transient_owner` for all 14 retained
registry cache roots and require it at the paused streaming-scope boundary.
Preserve the failure path's flat-row rollback and scope teardown. Per-module
symbols, ASTs and registration state remain reclaimable.

Regression: `test/01_unit/compiler/bootstrap/hir_registry_memo_transient_owner_spec.spl`
checks cached scalars, text and arrays across two reclaimed scopes, including
a new row inserted into an already-promoted dictionary, plus fail-closed
promotion outside a paused scope.

## Review of other fixes

Main `c9c9acd11c7` contains block-tail scalar lowering and additional metadata
containment. It is a broad HIR/MIR restoration, not an equivalent backport of
this ownership fix. Main `5d0f571671c` addresses missing collection ABI link
owners. Open PR #2044 reports a still-failing callback execution regression.
None is substituted for proof that this Stage 3 lane completes.

## Verification

Cycle 1: the compiler containing memo promotion passed native Stage 2 admission,
including bootstrap sanity and struct receiver/runtime capability. Its Stage 3
run crossed the previous failure sites and reached module 97/717. It exited 139
in `lower_hir_block+2060`, reading `0x12e0` through a type word of `0x12e1`.
The original runaway impl loop did not recur in this run. The ownership unit
regression still requires a qualified full-CLI test runner.

Cycle 2 preparation: adapt the scalar statement path from main's restored
block lowering. Keep tuple destructuring on the multi-result path. Preserve
present type metadata and normalize only absent type placeholders, rather
than copying main's unconditional type erasure. The native fixture
`test/fixtures/compiler/rc1_hir_block_tail.spl` covers implicit and explicit
returns, tuple destructuring, struct returns and both conditional branches.

The first fixed run also reported three unresolved `process_run` facade
imports and two unresolved file-lock facade imports. Point these callers at
their existing defining modules. The general frozen-surface resolution of
these facade re-exports remains an open compiler bug; the direct imports do
not claim to repair that language feature.

Evidence: `build/native_probe/config-layout/registry-owner-stage2.log`,
`registry-owner-stage3.log`, and `registry-owner-stage3-failure.log`.
macOS crash report: `simple-2026-09-29-094259.ips` (PID 42314).

Use `--jobs=full --incremental-unlimited` on this 10-core host. Reuse the
phase-owned caches; do not admit stub fallbacks or an old compiler as the
fixed artifact. Full Stage 3 completion remains the acceptance criterion.

## Cycle 2 result and remaining blockers

**STATUS: FAIL — draft checkpoint, not approved for landing or release.**

The current compiler passed Stage 2 bootstrap sanity and receiver/runtime
admission. The admitted Stage 3 resume completed its HIR sweep: 668 successful
modules plus 49 poisoned modules account for all 717 scheduled modules. The
collector reported 208 errors across 1012 logical sources; downstream passes
did not run. The native build exited 1, without the former imported-impl
runaway or the block-tail crash at module 97. This is progress, not a full
bootstrap PASS.

Top remaining groups include unresolved Token and Effect types, facade
functions such as dir_create_all/process_run/host_os, allocation helpers,
and the explicit unsupported generic struct/class methods gate (#158 Phase B).
The error-group artifact counts emitted per-module diagnostics; that output is
bounded and must not be confused with the collector's total of 208 errors.

A canonical-path, eight-source mini build importing
`std.io_runtime.{process_run}` resolved the facade correctly, including the
terminal callable. It then failed in post-monomorphization verification.
Thus the full-closure import errors are not proof of an absent facade export.
A first diagnostic fixture under a hyphenated path separately failed the
importing-surface lookup; the canonical-path result is the relevant import
reproducer. Neither mini build produced a passing native executable.

The checked-in block-tail fixture completes HIR 1/1 and crashes in
`PostMonoVerifier.walk_stmt+688` while copying a Let type payload. LLDB captured
`0xf198715900000001` as a supposed span pointer: the high word is the Some
discriminant (4053299545), and the copied source starts with an enum header.
`HirStmtKind.Let.type_` is declared as plain HirType while annotation producers
construct Some wrappers; consumers also disagree about optional handling.
This mismatch requires a coherent producer/consumer repair. The fixture
remains a failing regression, and the ownership SSpec still needs a qualified
full-CLI test runner. No verifier invariant was bypassed.

Additional upstream review: main's post-mono verifier projects HirTypeKind
before walker calls to reduce aggregate transport. Its frozen-registry
resolution work is substantially broader than this patch. Those changes
were inspected but not copied without matching verification.

## Performance and memory evidence

- Host: 10 logical CPUs, 24 GiB RAM. Stage 2 used all 10 workers.
- Stage 2 native ps sampling observed 3,277,328 KiB peak process-tree RSS
  (about 3.13 GiB); sampling began after startup, so this is not a lifetime
  maximum. CPU samples reached roughly 800–890 percent.
- Canonical Stage 3 admission pins one worker. `/usr/bin/time -l` reported
  852.44 seconds elapsed and 10,022,584,320 bytes maximum RSS (9.33 GiB).
- Fifteen-second ps samples observed 8,812,768 KiB peak RSS (8.40 GiB).
  Sampling can miss peaks; use the time result for the reported maximum.
- A 10 GiB RSS guard was installed for the owned Stage 3 process after the
  host showed 3.6 GiB swap use and only 3.7 GiB disk free. The build ended
  before the ceiling, without guard termination. Caches were preserved.
- Two debugger attachments briefly paused Stage 3. An attempted diagnostic
  setenv expression was rejected as ambiguous; it did not enable diagnostics.
  These timings are diagnostic measurements, not a controlled benchmark.
- The original 20–27.5 GiB runaway did not recur, but a 9.33 GiB failed HIR
  sweep is still a memory/performance concern. Full bootstrap memory bounds
  and end-to-end latency remain unverified.

The repository's bootstrap-progress-watch.shs reads Linux /proc and reported
zero processes/RSS for a live macOS compiler. That watcher was stopped and
replaced for this run with native ps process-tree sampling. Its zero-RSS
output is invalid evidence. A portable watcher fix remains open.

Evidence under build/native_probe/config-layout/:
`block-tail-stage2.log`, `block-tail-stage2-macos-resources.tsv`,
`block-tail-stage3.log`, `block-tail-stage3-failure.log`,
`block-tail-stage3-macos-resources.tsv`, `block-tail-stage3-error-groups.txt`,
`postmono-payload-crash.log`, `facade-import-canonical-diagnostic.log`.

No additional full rebuild is used to relabel the remaining failures as a
pass. Required compiler/lib/MCP checks, core/native smokes and the new SSpec
remain pending; landing and release are blocked.

## Scoped follow-up proposal after cycle 2

The block-tail fixture's `PostMonoVerifier.walk_stmt` crash has a concrete
producer mismatch: `HirStmtKind.Let.type_` is a plain nullable `HirType`, while
the four `Val`/`Var` lowering paths in `statements.spl` passed an explicit
`Some(HirType)` wrapper. Main corrected this representation in a broader
macOS bootstrap change (`35b22b6aedf`); that whole commit is not an exact
release backport. This isolated proposal sends the plain lowered type to
`Let` and retains the prior optional value at the symbol-table boundary.
The existing typed block-tail fixture exercises the affected path, but no
qualified exact-head executable is available here to run it. No additional
full Stage 3 cycle or positive result is claimed. The 208 collected Stage 3
errors remain separately unresolved; the retained summary does not support
attributing all of them to this Let representation defect.

## Cycle 3 preparation: optional Let annotations

Make the Let annotation explicitly HirType? and use bare lifted values from
the four val/var producers. Preserve absence through substitution, type
inference, effect/union inspection, MIR and post-mono verification. Backport
main's existing HirTypeKind walker transport repair and nil-name guards;
all unknown variants still fail with bounded E-MONO-031 receipts.

Regressions cover absent/present annotations, rejecting a leftover type
parameter, visiting an erroneous initializer under an absent annotation,
and preserving absence while substituting the initializer. The native
fixture now also checks an explicitly typed mutable binding.

Schema regeneration is pending. The configured release-path executable
identified itself as a Rust bootstrap seed and failed parsing the schema
generator dependency execution_metrics.spl (unexpected Indent). It was not
used again as normal tooling. The visitor generator strips optional node
suffixes, and the codec already encodes nullable nodes with presence tags;
their existing Let traversal/codec bodies therefore require no manual
change. The schema registry and fold digest still require a successful
generator run with qualified pure-Simple tooling before landing.

Further error review found that the loader manifest refers to a legacy
Effect enum whose full variant set is not declared by the current source.
The two currently declared Effect types are not compatible substitutes.
Main's lexer fix d55e104683c also changes Token.kind to a faithful wire-code
enum; its import edits cannot safely be copied alone. Neither blocker is
hidden with dummy types or removed validation.

## Cycle 3 verification result

Stage 2 admission passed on the optional-annotation candidate, including
bootstrap sanity and receiver/runtime capability. Native ps monitoring
observed 3,811,472 KiB peak process-tree RSS (3.64 GiB). Ten compiler workers
were confirmed by a process sample. Neither the 8 GiB memory ceiling nor
the 1 GiB free-disk reserve stopped the build.

The full checked-in block-tail fixture remains FAIL. It completes HIR 1/1,
then fails closed in value-struct layout validation with
`internal error: value struct layout owner module index is invalid`.
Exit 1, 0.76 seconds, 171,098,112 bytes maximum RSS. This happens before
post-mono verification and does not by itself prove the earlier crash fixed.
The relevant lookup is `owner_module_indices[walk.node_key]` in
`src/compiler/35.semantics/value_struct_layout.spl`; no layout guard was removed.

A separate scalar probe isolates tuple/inferred bindings and an explicitly
typed mutable binding. Exact source bytes are retained as
`test/fixtures/compiler/rc1_hir_let_annotation_scalar.spl`:

- Previous admitted Stage 2 producer: native compilation exits 139 immediately
  after the mono summary, using the identical scalar source.
- New admitted Stage 2 producer: native compilation exits 0; its emitted
  executable prints `optional let scalar probe PASS` and exits 0.
- Negative control changes the mutable-binding expectation from 42 to 43.
  It compiles, then exits 2 without printing PASS. The runtime checks are live.

The compiler explicitly reports the bootstrap-flat pipeline: normal MIR
lowering, borrow checking and flat MIR passes are skipped. These results
prove a narrow native bootstrap regression repair; they do not qualify the
full compiler, test runner or normal language pipeline. The SSpec cases
remain unexecuted. Producer and fixture hashes are recorded in
`build/native_probe/config-layout/optional-let-comparison.sha256`.

Building the actual schema-generator entry with the new pure-Simple compiler
was attempted in its own cache. It failed HIR on facade imports (including
dir_create_all and env/runtime helpers) and generic Future/Poll declarations.
No generator executable or regenerated schema is claimed. This confirms that
regeneration is currently blocked by remaining compiler failures, rather than
just a missing invocation.

Other-session review: draft #2051 binds parallel CLI/test-runner producers
after Stage 3 admission; its positive execution remains pending and it does
not change this bootstrap resume's one-worker requirement. Draft #2061 fixes
SHB reader/UI callback callers with execution pending. Neither is bootstrap
completion evidence. Upstream 43ead88be55 couples generic-template HIR handling
with MIR exclusion and a regression; deleting the current declaration fatal
alone would be incomplete.

**Overall STATUS: FAIL.** The three scoped rebuild cycles are exhausted.
Further rebuilds require an explicit decision under the repository's
AGENTS.md termination guard. No fourth full build or redundant full Stage 3
sweep was started. Pending: layout-owner repair, full-closure resolution,
generic-template backport, schema regeneration, SSpec/compiler/lib/MCP and
core/native gates, bootstrap completion, and reviewed PR landing.

Additional evidence: optional-let-stage2.log, optional-let-stage2-resources.tsv,
optional-let-stage2-sample.txt, optional-let-fixture-build.log,
optional-let-scalar-build.log, optional-let-scalar-run.log,
optional-let-scalar-old-producer.log, optional-let-scalar-negative-run.log,
and optional-let-schema-build.log under build/native_probe/config-layout/.

## Authorized continuation: reconciled Phase 3 / Phase 4 candidate

The user explicitly authorized continuing, local parallel work, fix PRs and
landing on 2026-09-29. This continuation is bounded to three further rebuild
cycles. Independent review/repair lanes ran concurrently; dependent compiler
generations and large builds remain serialized for memory safety.

The optional candidate remains preserved at `05b0d596d64`. Review found that
making `Let.type_` optional changes generated codec presence tags, so the
earlier assumption that codec bodies remain unchanged was incorrect. The RC1
reconciliation instead adopts PR #2059's plain nullable Let payload with a
separate boxed symbol-table annotation. It retains kind-only postmono walking,
guards absent Let annotations locally, and always verifies the initializer.
This restores the existing schema contract; optional schema regeneration is
no longer part of this reconciled candidate.

Grouped repairs under verification:

- Correct struct dictionary keys to `SymbolId` in value-layout validation;
  keep the owner-index guard and record the unexplained pre-HIR memory fault.
- Snapshot facade re-export item identity before nested native projections;
  retain a functional cache-hit/alias registration regression.
- Backport the complete core lexer wire-code conversion and all paired
  consumers, preserving RC1 UTF-8 spans.
- Backport generic declaration templating together with MIR non-emission;
  reachable unsupported generic use remains an error.
- Restore the manifest capability `Effect`/`AutoLeanMode` model and validate
  restricted capability combinations.
- Qualify the MIR folded-global helper with its receiver.
- Supply canonical planner admission to native CI; execution remains pending.

Cycle 1 uses ten workers, `SIMPLE_NO_STUB_FALLBACK=1`, an 8 GiB process-tree
RSS limit and 1 GiB free-disk reserve. Source diff and resource samples are
retained as `reconciled-cycle1-*` under `build/native_probe/config-layout/`.
Stage 4 readiness work may proceed concurrently, but actual Stage 4 needs an
admitted Stage 3 producer. No Stage 4 or landing success is claimed here.

Acceptance remains: native scalar and complete block-tail fixtures; positive
and negative value-layout fixtures; full Stage 3 and Stage 4 admission; real
SSpec and compiler/lib/MCP checks using a qualified full CLI; core and MCP
native smoke; required PR gates and reviewed landing. **STATUS: pending.**

### Continuation cycle 1 result

Stage 2 passed admission in approximately 21 minutes with ten workers. Sampled
peak process-tree RSS was 3,054,848 KiB (2.91 GiB); no resource guard fired.
Immutable producer: `phase1_1790649469_phase2_1790650801/simple`.

The reconciled scalar fixture compiled and ran successfully. Its changed-answer
control compiled and exited 2 with no PASS output. This validates the plain
nullable Let repair on the bootstrap-flat path only; normal MIR/borrow passes
remain excluded by that path's explicit warning.

The full struct/block-tail fixture still failed the owner-index guard
(0.68 seconds, 171,212,800 bytes maximum RSS). LLDB then proved that native
dictionary lookup finds the original SymbolId key but returns NIL for an equal
copied key. Cycle 2 therefore iterates typed struct values directly; the
general aggregate-key equality defect remains recorded separately.

The 87-source import probe improved to 11 poisoned modules and 17 errors
(27.05 seconds, 323,469,312 bytes maximum RSS), with generic declaration errors
removed but facade errors remaining. Disassembly showed inferred re-export
carriers reading incorrect field offsets. Cycle 2 gives those carriers explicit
nominal types and defining-module imports. No full Stage 3 sweep was repeated
while these smaller deterministic failures remained.

Removed the stale lexer enum/integer comparison discovered by review. Kept
postmono's robust/critical invariant unchanged and corrected comments that
overstated generic support. Added host-memory discovery and explicit-limit
contracts, and preserved Stage 4's admitted single-job continuation contract.
The shell contracts passed against the identical proposed files before their
application; no full bootstrap success is inferred from those checks.

Working direct-env and numbered-artifact guards passed; `doc/06_spec` executable
spec count was zero. Rebuilt layout/import proofs and full runtime/Stage 3/4
gates remain required. **STATUS: FAIL; cycle 2 repairs awaiting verification.**
