# Items 2, 4 and 7: Phase-3 continuation audit

Status: IN_PROGRESS; structural gate repair PASS; full feature verification incomplete.

## Session identity

- Owner: Codex `/root`; session `seven-items-247-20261020`.
- Worktree: `/home/yoon/dev/simple-seven-items-247-20261020`.
- Private branch: `work/seven-items-247-20261020`.
- Target: `refs/heads/release_phase3` on origin.
- Fetched base and expected target: `30e9aa83e94f557137dbceae22b27973d125d625`.
- Sidecars: N/A. Implementation and final review owner: root; review pending.
- Remote target rechecked after edits: same commit. Revalidate before integration.

The main checkout and the existing local release_phase3 worktree contain
unrelated changes and were not edited. Their local release branch is behind
the remote; neither is this lane's base.

## Retained scope and remaining work

The authoritative seven-item inventory is
[`seven_plans_host_completion_2026-09-29.md`](../../seven_plans_host_completion_2026-09-29.md).
All seven host-matrix rows remain TODO for certification on the fetched target.
This continuation prioritizes the user-requested items 2, 4 and 7 and does not
remove any other requirement or certify historical unexecuted test sources.

| Item | Existing authority | Remaining acceptance |
|---|---|---|
| 2 | `doc/02_requirements/feature/simple_distributed_textual_databases.md`; `item2_acceptance_matrix_2026-10-03.md` | Complete and execute the selected Authority A / Adapters A / Operating B / Retention A contract: durable atomic settlement, receipt/fencing and retry/readback, two-clone convergence/recovery, provider adapters, retention/security, host behavior and measured NFRs. Historical fail-fast scenarios and helper tests are not requirement PASS. |
| 4 | `doc/01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md`; `item4_riscv_phase4_matrix_2026-10-03.md` | Qualify real ELF/PE/Mach-O outputs and rejection contracts, compiler/application linking, relocations/archive/dynamic/TLS behavior, bounded execution and performance. The RISC-V matrix still explicitly leaves relaxation, dynamic RV64 and ELF32 driver work open. |
| 7 | `doc/02_requirements/feature/profile_switchable_container_algorithms.md`; `doc/04_architecture/compiler/profile_switchable_container_algorithms.md` | Execute PSC-AC-001 through PSC-AC-008, including independent attributed instances, full generic semantics, exact profile identity and measurements, guarded typed extraction/selection/lowering, workload A/B replay, explanation matching executed algorithms, and supported backend/host proof. Existing source contains more functionality than some older prose describes; broad completeness is unproved. |

## Current runtime evidence

Host: Linux aarch64. The installed
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple --version`
explicitly reports `this Rust-built Simple binary is a bootstrap seed only`.
It was not used for feature tests. The new worktree has no deployed `bin/simple`.
No source-matched Stage4 runtime was admitted in this session.

An independent build was confirmed live by process inspection, not a lock:
PID 3991659 executes `bootstrap-r16b/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple native-build`
in `/home/yoon/dev/simple-lane-boot6`. It was still `Rs` after about 90 minutes.
Do not restart, kill, modify, or claim this other session's candidate. Its
eventual result must be revalidated against this lane's source before reuse.

## Phase-3 structural gate repair candidate

The first run of `check-m3-phase2-phase3-production.shs` failed because it
expected the old inline root/path comparisons. Current production code calls
the shared Windows-aware canonical-spelling helper. After updating these
checks, the second attempt exposed a stale inline `cmp` expectation: current
bootstrap uses `bootstrap_stage3_require_equal "Phase 2 cache immutability"`.

The candidate checker now follows these current entry points and requires the
root and artifact-parent directory-chain guards. Six mutation cases were added
for these boundaries. The final bounded attempt reached:

```text
PASS baseline production structure
PASS mutation rejected: receipt-digest
PASS mutation rejected: owner-generation
PASS mutation rejected: root-generation
PASS mutation rejected: canonical-spelling-comparison
PASS mutation rejected: canonical-root
FAIL mutation survived: canonical-artifact
```

The mutation replaces the first canonical-path call at line 156; the same
spelling at line 204 still satisfies the whole-file grep. This demonstrates a
false-green structural oracle, not a runtime path failure. Next repair must
bind checks to each owning function, and mutation-test both artifact and
manifest call sites independently. Do not merely mutate every occurrence to
make the test green. Three verify/fix cycles were exhausted; this turn stops
per the repository guard. No passing command was rerun.

Raw logs for this session are `/tmp/seven-items-247-phase3-production-20261020.log`,
`/tmp/seven-items-247-mutations-20261020.log`, and
`/tmp/seven-items-247-mutations-final-20261020.log`.

## Continuation and landing gate

The two changed shell files are an unverified repair candidate, not a finished
implementation. No commit, push, PR, release-ref movement or full Phase-3 PASS
was performed. First repair the function-scoping oracle in a bounded follow-up;
then admit a source-matched runtime, execute the retained requirements, repair
production gaps and generate SPipe evidence/manuals. Run required verification
and obtain STATUS: PASS before submitting the exact owned head through the
protected integration authority. A structural baseline alone never certifies
Phase 3 or any of items 2, 4 and 7.

## Scoped gate repair follow-up

The continuation replaced whole-file canonical-path searches with
`require_in_function`, which searches only the named top-level Simple function.
Artifact and manifest spelling and parent-chain guards are independently
required. The mutation harness accepts an optional function scope and removes
one guard only inside that owner. Existing first-occurrence mutations retain
their prior behavior. The bootstrap immutability check follows the current
shared equality-helper call rather than requiring its superseded inline cmp.

`sh scripts/check/check-m3-phase2-phase3-mutations.shs` passed its baseline and
all **24/24** mutations, including both canonical-path and both directory-chain
removals. The checked-in [raw output](items247_phase3_scoped_mutations_2026-10-20.md)
is the evidence for this bounded repair. It supersedes the earlier surviving
mutation as the current structural-gate result; the original failure remains
above as provenance. This is a source-structure check, not runtime execution.

Current-state inspection also confirms the broad item-2 SPipe specification
still contains explicit UNIMPLEMENTED replica, settlement, evidence, bridge,
and retention helpers. They must be replaced with complete production-backed
fixtures and oracles; passing this gate does not waive those obligations.
The independently owned Stage3 compiler PID 3991659 remains live. No full
feature PASS, source-matched Stage4 admission or landing is established.

## Live GitHub reconciliation after user correction

The user requested checking GitHub because much of the feature work may already
be done. Fetched `origin/release_phase3` remains
`30e9aa83e94f557137dbceae22b27973d125d625`. The old host matrix is a
certification inventory, not an implementation inventory. Earlier remaining-work
lists in this audit must not be read as assertions that those owners are absent.

| Item | Confirmed landed implementation | Remaining evidence / explicitly retained gaps |
|---|---|---|
| 2 | [#2286](https://github.com/ormastes/simple/pull/2286) implements the distributed DB core and durable adapters; [#2306](https://github.com/ormastes/simple/pull/2306) adds paged settlement and queue-v2 recovery. They merged originally into release/1.0; `git merge-base --is-ancestor` confirms both queue `d2ca5cfe56d` and paged `56c15e77044` implementation commits are ancestors of current release_phase3. | PR bodies explicitly retain protected production settlement, cross-replica fencing/delivery, scalable retention, historical-query/migration work and full system oracles. Authored Simple tests were unexecuted in those receipts. Current source must be compared with each gap before implementing it again. |
| 4 | [#3688](https://github.com/ormastes/simple/pull/3688) fixes generator hex addresses and NOBITS/NOLOAD. [#3935](https://github.com/ormastes/simple/pull/3935) reports mold-safe full-CLI linking and internal ELF hello execution. | The earlier #3505 generator implementation blockers are superseded. #3688 retained runtime/docgen/real-script qualification. #3935 records internal full-CLI input-loading OOM; its projection implementation is Rust, and hello/link evidence is narrower than the retained complete linker/host/resource contract. |
| 7 | [#3073](https://github.com/ormastes/simple/pull/3073) merged adaptive containers, capture/replay, guarded literal-membership lowering, filter selectivity and observed set-loop capture. [#3784](https://github.com/ormastes/simple/pull/3784) binds explicit target identity under default collection policy. | #3073 explicitly leaves general compiler-loop instrumentation, broader typed/profile joins and complete provenance unfinished; full Simple acceptance was unrun. [#3504](https://github.com/ormastes/simple/pull/3504) distinguishes merged implementation from failed historical qualification. #3784 also retains target-omitting legacy loader paths and eight unrun scenarios. |

Live GitHub Actions inspection for the exact current head returns one completed
`publish` check with conclusion `skipped`. The latest eight branch workflow runs
also have conclusion `skipped`. This provides no successful Phase3 qualification
receipt. Neither merged PR state nor skipped publication proves whole-feature
acceptance. No completion percentage can be justified from these records.

Next implementation work must start from these landed owners and investigate
only confirmed remaining gaps. Do not recreate the database queue, generator
repair or guarded literal-membership consumer based on the stale umbrella text.

## Item 2 REQ-014 source implementation continuation

The three broad causality scenarios no longer call the generic UNIMPLEMENTED
settlement checker. Their oracles exercise the existing production durable
queue, independent fixture arrival orders, canonical batch-ID tie-breaking,
original signed patch bytes/dependencies, receipt-parent ancestry, actual
remote snapshot accepted counts/allocator state, missing-dependency refusal
and unchanged remote refs. A new worker reopens every persisted generation in
a fresh process and compares its actual head and encoded-content digest under
an independently decoded policy pin. No process/provider result is mocked.

This implements missing SPipe acceptance wiring rather than duplicating landed
queue scheduling. Both fixtures are disposable bare local authorities; no
protected publication claim follows. Test sources, test-plan addendum and a
stale-manual annotation are updated. Runtime execution and generated manual
remain pending because no source-matched Stage4 runner has been admitted.
Do not infer PASS from source review or whitespace checks. Existing item-4/7
implementation and qualification scope remain intact.

### Causality oracle identity review

Source review tightened the child-process trust boundary: the admitted runtime
is now a typed record with exact binary and provenance hashes, checked before
and after every process invocation. Child stdout/stderr, exit status and queue
head/digest are retained with those identities when execution becomes possible.
The REQ-014 runtime admission still happens once at suite entry, and the tests
remain UNEXECUTED pending a qualified candidate.

The existing Stage3 process PID 3991659 was revalidated live at about 100 minutes.
Its actual stdout log at
`bootstrap-r16b/logs/aarch64-unknown-linux-gnu/stage3-native-build.log` reached
`[mir-lower] lower_module:done`; no terminal build success or executable was
present. This is progress evidence for another owner's ongoing build, not
Phase3 qualification. Bounded checks of canonical release/Stage4 locations in
boot6, stage4c and the combined-runner worktree found no deployable candidate.
No duplicate compiler build or mutation of those lanes was performed.

## Release_phase3 implementation direction and refreshed base

The user explicitly requested implementation against release_phase3 followed
by a passing Phase3 compile before landing. The private branch was rebased onto
remote `23085fbde5b` (the exact full ref is recorded by Git). Existing work and
history are retained; no protected ref was moved. The earlier boot6 compiler
ended with `shutdown-unverified-lock-retained`. Its later independently owned
corrected-compiler probe also reached terminal timeout (exit124, quiescent=1).
Neither result is a compiler PASS; neither lane or cache was modified here.

The current release source's fixed per-channel checkpoint reservations were
confirmed in `checkpoint_reader.spl`. A new budgeted store read API now bounds
reads by remaining capacity and returns actual encoded byte charges, including
HEAD. Empty channels consume zero; corrupt and over-limit states fail closed.
Checkpoint reads share the smaller remaining IO/work limit and accumulate
actual charges. Five new regression scenarios and a real native probe cover
this path. Earlier maximum-reservation quota fixtures were updated to express
zero-IO refusal and shared policy/metadata work rather than obsolete maxima.
Full resource/host requirements and page/policy budget work remain open.

The first native probe compile refused `compile-event-journal-missing`, before
compilation. The diagnosed retry initializes the isolated checkout's SCV
inventory through `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, using the admitted producer
SHA256 `645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a`.
The owned compile has a 300-second deadline and 8GiB cap. Input hashes, logs,
cache and process receipts reside in `build/native_probe/items247-store-accounting/`.
No executable acceptance or Phase3 PASS is claimed before its terminal result.

### Terminal bounded compile outcome

The cold-initialized attempt completed HIR for 197 modules, then was stopped
and proven quiescent after identifying the probe's nonexistent `app.io.mod`
`mkdir_p` import. Both that probe and the causality fixture now use the actual
`dir_create` facade. The corrected attempt completed HIR and monomorphization,
then **FAILED MIR**: 188 modules succeeded and 9 failed, with 18 distinct
reported diagnostics. Its process receipt records exit1, peak RSS5026400KiB
and quiescent=1. No probe executable was produced or executed. The three
bounded command attempts are consumed; no further retry was started.

The [grouped diagnostics](items247_store_compile_diagnostics_2026-10-20.md)
identify missing struct equality in the probe and existing DB owners, a
multiple-wildcard match error in db_page_decode, and gzip/header text-byte
iteration lowering errors. Source locations also retain both old/new frozen
SCV roots: the current probe exists in revision67987af4, while the old probe
exists in revision7fd5d913. This is a cache/source-origin follow-up, not proof
that source locations all describe current bytes. Native equality and wildcard
issues are related to existing tracked bugs; no fieldwise workaround or
placeholder pass was substituted to make the probe appear green.

Next work must repair these compiler/DB prerequisites or use a refreshed,
qualified pure-Simple producer, renew source/cache provenance, then compile and
execute this probe and the full retained acceptance scope. Phase3 remains
FAIL/unqualified; no work ref was pushed and nothing landed. The current
implementation remains a reviewable candidate, not a completion claim.

### Compiler prerequisite continuation: gzip proof and literal-pattern repair

The [current prerequisite report](items247_gzip_and_suffixed_patterns_2026-10-20.md)
records a compiled-and-executed native gzip-header proof, plus the authored
compiler fix for suffixed literal patterns becoming wildcards. This resolves
the gzip `.bytes()` typing blocker within the standalone five-module probe;
full system acceptance and the compiler repair remain unverified. The existing
native array fixture issue was kept separate from header content correctness.
Current release source already contains item4's packed-byte input implementation
(e69519b2d9c); old widened-input prose is historical, not missing-source proof.
No full Phase3 PASS or protected integration occurred in this continuation.

### Struct inequality RED and database operator ownership

A standalone one-module native fixture reproduced a narrower compiler defect:
Eq accepted the existing user __eq__, whereas NotEq failed at its sole operator
site. The repair routes NotEq through the same method and negates exactly once;
three MIR regressions and a custom-relation native fixture are authored.
See `doc/08_tracking/bug/struct_inequality_missing_equality_dispatch_2026_10_20.md`.

The six named database value records now define explicit equality owners, with
field and byte-content semantics rather than pointer equality. Five source
scenarios cover their independent fields and optional identity shapes; none
claims authentication or automatic equality for arbitrary types. Policy
configuration equality remains an explicit prerequisite. All new tests remain
UNRUN; no full Phase3 or integration PASS is inferred from source authoring.

The boot7 Stage2 producer29dd8539 was found admitted with a passing sanity
receipt, while its independent full phase-verification process remains live.
It does not contain this session's compiler patches. The source-refresh cache
path pins Rust dependency-key owner5e566362, but this base has e425a0af; that
refresh path cannot be used or weakened. A separate canonical fresh-source
bootstrap is needed to build these compiler fixes, preserving all other lanes.

### Checkpoint policy pin prerequisite

Checkpoint authentication now compares the independent authority policy pin with
the paged configuration pin, then retains mandatory manifest/policy validation.
That validator calls db_policy_encode, which hashes the full configuration body
and rejects a copied revision on a changed body. This avoids arbitrary record
equality and adds no extra canonical encoding to the existing validation path.
Three authored scenarios cover the valid signed paged checkpoint, changed body
with copied pin, and changed valid policy with a recomputed pin. Tests remain
UNRUN pending the owned producer; no Phase3 or integration PASS is claimed.

### Owned producer build: terminal preflight failure

Candidate source repair commit: `0160c81e827`. Owned build root:
`.simple/storage/build/bootstrap-items247-v1`; logs:
`build/native_probe/items247-bootstrap/`.

The initial LLVM discovery refusal was resolved by selecting installed
LLVM 23.1.2 via LLVM_SYS_231_PREFIX. The canonical fresh bootstrap built the
Rust seed in 3m55s, native-all in 2m58s, runtime-nolto in 46s and compiler
backfill successfully. These are bootstrap prerequisites, not a qualified
Simple tool or Phase3 proof. The seed check, ByteOrder lazy-import probe and
marker checks passed. Preflight then failed `disk-space(19GiB<20)`.
The process-tree receipt is terminal `status=complete`, exit1, peak3357824KiB;
all owned children were quiesced. Cached outputs (~3.5GiB) were retained.

A bounded cache-preserving retry with an outer 16GiB threshold still failed
before Cargo: the independent preflight enforces 20GiB. That gate was not
modified. No more retries in this continuation; free sufficient disk before
resuming this exact owned cache. Other sessions' files/builds were preserved.
No Stage2 admission, Phase3 compile PASS, qualified regression execution or
protected integration was produced. New source tests remain UNRUN.

### Owned producer admitted; inequality native GREEN; imported owners RED

The owned cached bootstrap resumed after disk recovery. All 1400 Stage2 modules
compiled with zero failures (1029.4s compile +23.2s link). Sanity passed ordinary
and bootstrap modes, struct/runtime capability admission completed, and the
immutable capsule verified. Producer SHA:
`bf3f9b39f466576febfff5459f4cea175e93c439802543f92a8f710d11076ccb`.
Its source snapshot d22288b4a4c6c542c6c01ed88fd8b8d5d51632325a67c5dfa5ec9ecbd6916514
matches the parent candidate's critical compiler and checkpoint edits.

The same-module native inequality fixture compiled and executed successfully,
stdout `STRUCT_INEQUALITY_NATIVE: PASS`, exit0. Evidence is retained under the
parent worktree's `build/native_probe/items247-struct-inequality/bf3f9b39/`.
The store probe remains RED: HIR197/197, MIR191/197, eleven unique imported-owner
operator diagnostics. Its five inspected SCV source snapshot files match the
candidate. No typed-pattern wildcard or policy-comparison diagnostic recurred.

A two-module native fixture isolated the imported-owner error for both equality
and inequality. Repair and three MIR regressions are authored in a second owned
worktree `simple-items247-import-eq-20261020`, based on the exact parent head,
so the live parent Phase2 verification retains unchanged source. See
`doc/08_tracking/bug/imported_struct_operator_owner_lookup_2026_10_20.md`.
The source repair is not yet qualified. No full Phase3 PASS or landing exists.

### Imported-owner producer refresh: observer failure, then disk preflight

The new candidate bootstrap built its Rust seed in2m14s and native-all, then
its extra outer RSS observer aborted on an exiting timeout zombie's negative
process-group/session values in /proc/stat. Receipt: rss-measurement-failed,
exit89, peak3528116KiB, quiescent1. Caches were retained. This did not establish
a compiler error or a memory-limit breach.

A retry under a real kernel memory scope (32GiB, swap0, wall3600s), preserving
all canonical bootstrap guards, stopped at disk preflight19GiB<20. See
`doc/08_tracking/bug/bootstrap_rss_observer_exiting_zombie_stat_2026_10_20.md`.
The imported-owner source repair still has no rebuilt producer or native GREEN.
The earlier parent producer's full-CLI qualification remains a separate live
job, with a2777-module HIR closure; its outcome must not qualify this patch.
No full Phase3 PASS or landing is established.

### Imported owner compile repaired; record-element runtime RED

A kernel-scoped cache-preserving retry completed seed/runtime preparation in71s,
preflight passed all five checks, and the next Stage2 compiled1400 modules with
zero failures (526.9s compile+31.1s link). Admitted producer699083c7 has a verified
runtime capsule and a source binding matching the imported-owner patch.

Its two-module native fixture compiled successfully and passed the parameter
checks, but exited14 at record-array-element inequality. Disassembly proves a
raw cmp after rt_array_get with no __eq__ call. The typed owner was available,
but the gate required a MIR Struct representation. The new source candidate
uses declared record provenance for runtime handles and preserves arithmetic
result layout names separately. Six MIR scenarios and the expanded native
fixture are authored; the latest changes remain unverified.

The store closure improved to MIR197/197, zero failures, then hit the extra
8GiB probe guard at peak8393008KiB (exit88, quiescent1). No store executable or
runtime PASS resulted. Broader qualification of the known-failing699083c7
candidate was stopped through its exact owned kernel scope, exit143; caches
and immutable admitted artifacts were preserved. See
`doc/08_tracking/bug/record_array_element_operators_compare_handles_2026_10_20.md`.
No full Phase3 or feature PASS, protected ref movement, or landing occurred.

## Typed-record bounded candidate terminal result

See [the current qualification receipt](items247_typed_record_candidate_2026-10-20.md).
Fresh Phase 2 admission and the imported-record native probe passed. The store
closure failed MIR in 9/197 modules on identity-wrapper operators. The owned
full-CLI qualification was stopped, caches retained, and no Phase 3 PASS or
landing is claimed. Reconcile the fetched upstream structural-equality owner
before a new bounded candidate.

## Reconciliation with upstream d9e177de79a

The private branch was rebased onto fetched release_phase3
`d9e177de79ac599ecd4b165e39c26d99f037c357`; all 16 owned commits replayed
without textual conflicts. The prior candidate is preserved on
`work/items247-pre-reconcile-20261020`. This updates source only and renews no
runtime evidence. No protected reference was moved.

Semantic review found one stale unit-test expectation: a provider without
`__eq__` previously required an unresolved-operator diagnostic. Upstream
`90d1f293648` adds structural equality. The test now requires successful
lowering, zero custom equality calls in the method-less provider's consumer,
and the exact first-provider equality call in the custom consumer. This keeps
provider isolation while honoring the new language contract. The updated test
is authored but unrun.

The combined compiler retains upstream structural fallback and this lane's
qualified-owner custom dispatch. Clean rebase is not proof that they compose
correctly; runtime qualification remains mandatory. No fourth compiler
repair/rebuild cycle was started after the bounded candidate failure.

## User-authorized six-cycle continuation

The user explicitly said `go 6times` after the three-cycle stop. The limit is
now six total cycles; this reconciled candidate is cycle 4, not a reset.
Fetched target remains d9e177de79a. The prior producer's binding is incompatible
with the reconciled runtime (including the packed-i64 revert) and compiler
source. Its sealed capsule, cached objects and terminal evidence remain intact.
A separately bound cycle-4 output is required; no stale identity stamp is
rewritten and no already-green unchanged probe is being repeated as proof.

## Cycle 4 terminal result and cycle 5 correction

Producer ef2d27014457e1da10ca5151899503fb491e474ac7b75a7d75cf9db591c34665
compiled 1401 modules without failure, linked, passed both sanity modes and
Hello World, and passed the custom imported-record native probe. The store
closure failed 9/197 MIR modules on identity-type operators; full qualification
was stopped and caches retained. No Phase 3 or whole-feature PASS is claimed.

The [reviewed layout-owner correction](../../../08_tracking/bug/binary_structural_equality_callable_layout_identity_2026_10_20.md)
is authored with distinct-layout same-name-provider native regressions. This is
cycle 5 of the user's six-cycle limit. Qualification of the correction is pending.

## Cycle 5 terminal result and final cycle 6 correction

Cycle-5 producer 9ce404cd5e5383a62cdc06c1e0f84152a9b07e057f5bd34266fac116025c1cc8
passed Phase 2 admission and lowered the store closure's MIR 197/197 without
errors. The expanded native regression compiled but exited23, and direct field
checks compiled and exited28 under that same producer. Source review confirms
that Struct construction still borrowed a bare provider layout while equality
used its exact declaration. The shared constructor and direct-call route now
retain the exact layout; authored assertions cover declared aggregate order,
all fields, literals and reversed providers. See the
[constructor bug report](../../../08_tracking/bug/imported_struct_constructor_borrows_bare_provider_layout_2026_10_20.md).

Cycle-5 full-CLI qualification and the separate provisional Phase 3 diagnostic
were stopped; the latter never completed. Caches and receipts remain retained.
Cycle 6 is the final user-authorized repair cycle; its runtime and Phase 3
results are pending. All broader item2/4/7 requirements remain retained.

## Six-cycle limit reached: current terminal result

See [the final authorized cycle receipt](items247_cycle6_terminal_2026-10-20.md).
Phase2 admission and Hello World passed; the native regression compiled and
failed at exit22 on the last field after specific constructor checks passed.
A bare-name parameter-copy path remains open. All owned builds stopped and
caches were retained. No seventh source repair, Phase3 PASS, push or landing
was performed. The full selected item2/4/7 scope remains unfulfilled.

## Resumed cycle7: qualified parameter-copy correction

The user approved the proposed three additional cycles with `go`; limit9.
The branch rebased onto fetched release_phase3 3ce093ea597 without conflicts.
Qualified Struct parameter layouts and local HIR metadata transfer are authored
with complete-copy MIR assertions. The native exit22 regression is preserved.
The previous six-cycle terminal report remains historical evidence, not a
claim that the user extension was unavailable. New qualification is pending.
