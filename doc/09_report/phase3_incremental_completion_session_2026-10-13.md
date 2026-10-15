# Phase 3 incremental completion session

Status: ACTIVE / INCOMPLETE. Implements the execution lane for the [completion plan](../03_plan/compiler/phase3_incremental_build_completion_2026-10-13.md); no Phase 3 completion or incremental speedup claim.

## Ownership and inputs

User authorized takeover of the idle sync worktree. Its previous branch and 61 local commits were preserved. The session uses `work/phase3-incremental-completion-20261013` at `3f5200fd34d9a205381a592c3fec6304fa058c4b`; target is `origin/release_phase3`. Ownership is recorded in the worktree Git metadata as `spipe-session.json`. Other dirty worktrees and active builds remain outside this lane.

The pure-Simple Stage 2 producer is frozen under the private evidence root below, SHA256 `4812f6ed17fe51ef0bd36fdd5d6f02d2871d7f6c14a9b468bed209016f33be77`. Parent provenance and sanity agree with those bytes. The currently deployed host binary identifies itself as a Rust seed; see [tooling bug](../08_tracking/bug/deployed_simple_is_rust_seed_2026-10-13.md). No seed fallback was installed.

## Phase 3 diagnostic

Private evidence root: `.simple/storage/build/phase3-incremental-completion/`. Producer, argv, selected environment, progress log, maximum RSS, watchdog receipt, and terminal status are retained there. One worker, 3 GiB enforced tree RSS cap, 1800-second external deadline. This direct diagnostic is non-admitting and cannot replace authenticated Stage 3 provenance.

Attempt 1 failed source admission in 4.17 seconds: `plugins.backend_registry.full_static_backend_registry` and `plugins.backend_vhdl.driver.driver_aot_vhdl_output` were tracked but omitted from the sparse worktree. The failed result is retained under `attempt1-source-admission`. Materializing the tracked plugin subtree changes the failed input; attempt 2 is running. No compiler source repair or successful object count is claimed yet.

## Completion requirements

Still required: required compiler closure with authenticated objects; genuine compiler link; compiler-built/executed Hello World; every incremental feature and historical acceptance scenario; supported Phase 4 build/sanity evidence; applicable verification and performance gates. Six native test-product builds remain user-deferred. No push before Phase 3 qualification; no overall PASS from partial diagnostic results.

## Evidence retained during attempt 2

Snapshot time: 2026-10-13T03:48:06.690909+00:00. Source admission passed after materializing the tracked plugin subtree; frontend surface processing remains live. `evidence/owned-source-inputs.json` binds 11,143 owned Simple source files; manifest SHA256 `e62220256d260ba817fe375b8bcd3d577cf147219953c1a1ae09e89d1e58b086`. The initial `acceptance-ledger.json` contains 34 requirement/feature rows, all NOT_YET_VERIFIED; historical scenario coverage remains required beyond this initial ledger.

Both required direct-env guard scopes (`--working`, `--staged`) returned `STATUS: PASS` once. No Simple source was modified, so these narrow guards do not imply compiler or feature qualification.

The retained Stage 2 Hello World log warns that bootstrap-flat builds skip MIR lowering, borrow checks and flat MIR passes for modules outside the bootstrap entry. A later successful Stage 3 diagnostic must be audited against the required genuine compiler closure; this route alone cannot prove complete tree validation. Do not count that warning as a successful full compiler gate.

## Attempt 2 terminal evidence and final bounded attempt

Attempt 2 exited 88 after 1220.54 seconds: the watchdog enforced its 3 GiB cap at 3,164,560 KiB observed peak RSS. It proved descendant quiescence. No compiler binary exists. Last HIR progress: 546/1293 modules. Durable HIR snapshots tracked approximately 646 MB live heap against approximately 3 GiB RSS; allocator retention, untracked allocations and graph ownership require investigation, and none is asserted as the root cause. Logs, memory snapshots and resource/terminal receipts are retained under `attempt2-hir-rss/`.

Host available memory subsequently measured 67,253,432 KiB. Attempt 3 retains the same frozen producer, pinned source and cache authority, and raises the explicit diagnostic process-tree cap to the existing 8 GiB compiler ceiling with a 7200-second external deadline. It does not claim a compiler optimization or improved memory behavior. Preserve the valid cache prefix; do not rewrite producer/source keys. This is the final permitted attempt in the three-cycle lane; a remaining failure must be reported and repaired from its evidence instead of starting a fourth equivalent run.

The failed HIR run now has a bounded growth cohort in `evidence/attempt2-hir-growth-samples.json`, derived from the retained durable per-source snapshots. These are RSS and tracked-live-heap observations, not allocation attribution or a performance improvement claim. Attempt 3 was verified live at supervisor PID 1008337 during frontend surface construction. A fourth equivalent run remains prohibited.

## Native artifact-owner authority qualification

The current production `compiler_artifact_service.service` already guards wrong-action results and foreign/stale leases. The RED description in the historical service-refinement SSpec refers to its captured c48 source, and is not a current-source failure claim.

`test/fixtures/compiler/artifact_service_authority/main.spl` imports the production profile, protocol and owner implementations. On the pinned pure-Simple Stage 2 producer, it compiled 14 modules using Cranelift on Linux AArch64, linked, and ran with exit 0. Wall time: 25.468 seconds for this cold diagnostic; no compile-performance target is claimed. Actual output: `artifact service authority: wrong action, stale lease, duplicate claim, immutable input passed`. Producer SHA256 `4812f6ed17fe51ef0bd36fdd5d6f02d2871d7f6c14a9b468bed209016f33be77`; executable SHA256 `99722107ea292295cec5aaef5f6ecab28e1c831cdb1796126ecc26e02658a8cf`; fixture SHA256 `78d0d6549cf16506e2986c90aa80826ef67333bd243291e04f34cb89ba401272`; production owner SHA256 `602830525a67d14151f3514119142f90962231bcdb0f0a7f9b4c778ceb42d7ed`.

Evidence: `artifact-service-authority/evidence/result.json`, argv, resource/watchdog receipts, build log and actual stdout/stderr under the private evidence root. REQ-IM-007 and the async ownership matrix row now have PARTIAL_NATIVE_EVIDENCE. Real concurrent publishers/waiters, cancellation/crash/SCC recovery, runner integration and formal refinement remain unverified. These four passed native transition criteria must not be replayed unchanged in this session.

## Controlled changed-entry object-cache baseline

A private copy of the three-file native-cache integration fixture compiled and executed all three observed source generations with correct outputs 42, 44 and 46. The controlled generation 1 -> 2 body edit retains identical observer paths, producer/backend/runtime/cache/entry authority and unchanged dependency sources. Both report zero reused and five rebuilt module objects. The final cache index retains only an entry source row with an empty witness. Root cause is not established; current-source cache improvements require a coherent successor.

This is an incomplete direct-native baseline, not prepared TLDR performance qualification. Cold wall time: 18.9605 s; controlled generation wall times: 3.5609/3.6294 s including link. No p95 or 100 ms claim. The observer-refusal failure and the earlier observer-path confound remain explicit in [the canonical cache qualification blocker](../08_tracking/bug/pinned_stage2_changed_entry_cache_rebuilds_dependencies_2026-10-13.md). The bounded probe is closed after the corrected control; its passing semantic outputs must not be replayed unchanged.

## Final Phase 3 diagnostic outcome

Attempt 3 completed HIR for all 1293 modules but exited 88 at the 8 GiB RSS guard during the next monomorphization phase, after 1678.67 seconds. No compiler executable exists. Peak observed tree RSS: 8,390,084 KiB; cap: 8,388,608 KiB; descendants quiescent. This is a terminal failed compiler build, not a Phase 3 PASS or an authenticated-object total.

The three-attempt lane is exhausted. [Canonical monomorphization blocker and concrete repair handoff](../08_tracking/bug/phase3_monomorphization_rss_cap_2026-10-13.md) records source/producer identity, HIR boundary, retained artifacts and the corrected-producer qualification path. No fourth equivalent automatic run, no rewritten cache authority and no push. All unmet requirements and the full original optimization/Phase 3 scope remain active.

## Corrected next repair boundary

Current source explicitly excludes `SIMPLE_BOOTSTRAP=1` from archive-backed HIR production and requires an actual selected managed-runtime owner. Rebuilding current producer bytes alone is insufficient to select the bounded path in Stage 3. The canonical memory blocker now records the bootstrap-compatible ownership/admission work needed before a new full-tree qualification. No guards were relaxed and no extra build was launched.

## Authorized parallel repair continuation

The user subsequently requested parallel memory and logic fixes, followed by checking generation of all required objects and genuine linking. This authorizes parallel source repair and one additional changed-producer qualification cycle. The existing three attempts and their evidence remain unchanged; the new cycle must contain the reviewed repairs rather than repeat the old producer or increase its memory ceiling. The private session-state records this extension.

Memory ownership is assigned to `monomorphize_integration.spl`; object/cache identity ownership to `driver_aot_native_output.spl`; canonical producer preparation and the final compiler qualification are coordinated separately. Independent lanes use distinct writable outputs. Current findings are candidate repairs, with no new compiler, object-total, link or performance PASS claimed. No push is permitted before Phase 3 qualification.

The frozen memory candidate additionally introduces signature-only discovery in `mono_archive_types_v1.spl`, deferring complete executable-body canonicalization until a deduplicated concrete request. Independent review accepted the signature, nominal ownership, method-bound-parameter and linkage invariants. Actual RSS and executable regressions remain pending. Both direct-env guard scopes passed with the changed production sources.

Canonical producer refresh is running with the copied seed's exact fingerprint and byte authority. Its first preflight refusal was preserved; materializing `src/package_ownership` and `examples/10_tooling` corrected source admission. The wrapper reused the seed and started Stage 2 compilation in the private `phase3-producer-refresh` output. One build worker and the enforced 5,859,375 KiB inner process-tree ceiling remain in effect; no new Rust build or source modification during compilation.

Read-only route review corrected an earlier assumption: supplying `--entry` does not by itself bypass the bootstrap fixed-MIR shortcut in normal `aot_compile`. `SIMPLE_BOOTSTRAP=1` without the supported full-pipeline selection can still emit entry-only MIR and skip borrow/full MIR passes. A successful flat bootstrap link must remain explicitly limited; the requested all-required-objects qualification must select the genuine full pipeline and authenticate its inventory. This is not justification to remove archive/runtime ownership guards.

## Complete linker transport candidate

Final linker and hosted C-driver paths converted argv into a shell command. With 4 KiB pages this host limits an individual argument to 128 KiB, which a large exact object inventory can exceed despite remaining below total `ARG_MAX`. The reviewed source candidate routes all four final execution sites through the existing bounded direct-argv facade, retaining object membership, tool identities, strict admission checks and exit status. Capture is 64 MiB with explicit truncation markers; no new internal deadline is introduced.

The selected `core-c-bootstrap` runtime contains both the tuple adapter in `runtime_native.o` and raw owner in `runtime_process.o`; looking only in `libsimple_native_all.a` would give the wrong availability conclusion for this profile. The focused native transport fixture failed before link on older-producer module-static/body-free backend limitations (29 objects succeeded, 14 failed). It did not execute assertions or qualify transport; its first invocation also used default frontend/HIR cache locations, which are recorded as a scope limitation. No shared cache was deleted or rewritten.

The first producer build was stopped deliberately to include this discovered link repair. It left 1,001 object files and a canonical writer lock; quiescence and every interrupted receipt are preserved. [Canonical writer recovery is unavailable](../08_tracking/bug/interrupted_bootstrap_cache_writer_recovery_unavailable_2026-10-14.md), and relocating the cache changes its link-compat authority. The safe restart uses a fresh private native cache under `phase3-producer-refresh-linkfix`, with the same seed and all five source repairs. No predecessor object-reuse claim or new Phase 3 PASS is made.

The Mono source probe likewise remained incomplete: the 300-second total budget ended with HIR 144/381, peak RSS 1,132,376 KiB, timeout exit 124 and descendants quiescent. Its source/profile/cache prefix, path refusals and mistaken cancellation are retained; no executable assertions passed.


## Local landing checkpoint — 2026-10-15

The user requested landing. This checkpoint preserves only the five original compiler/linker repairs, the six reviewed remaining-version admission owner files, their authored specifications/fixtures, and the session reports. The twelve larger perf/memory lane drafts remain ignored, incomplete, and excluded from this checkpoint. This is a local review checkpoint, not a release or Phase 3 completion claim.

The seed-produced Stage 2 candidate compiled 1,344 objects and linked; that is producer preparation, not the requested pure-Simple full-object qualification. The candidate metadata expectation, runtime receiver, and composed retained sanity controls passed. Mandatory matrix attempts stopped before compiler rows: nested campaign session escape (90), MC/DC delegation preflight (2), and omitted outer TMPDIR (125). Each enclosing owner reported quiescence. The third setup error was the root agent's mistake. The corrected hash-pinned launch exists, but execution requires the explicitly requested three-cycle-limit extension. No original green controls need replay.

New feature SSpecs remain UNRUN; independent static review does not establish physical RSS reclamation, all-object membership, final link/Hello, or the latency target. Compiler/core/lib and MCP/LSP readiness checks remain pending. No STATUS: PASS, merge, release, or push is authorized by this checkpoint.

Committing changes Git provenance, even when source bytes remain identical. The old closed-profile resumption must not be presented as valid against the new Git state without a reviewed provenance transition. Original receipts, pre-commit state, and exact patch are retained in ignored local landing evidence.

## Authorized corrected matrix attempt — 2026-10-15

The user requested “go fix land”. The exact commit-only provenance bridge and corrected matrix launcher passed independent static review. The real nondelegated MC/DC matrix reached full CLI compilation under the canonical enforced 8 GiB root supervisor. It failed with exit 88 at parse progress 816/2673, peak tree RSS 8,390,944 KiB. The supervisor reported quiescent=1 and no unexpected session PIDs. No full CLI/test host was produced, no test suites ran, and no all-object/link or performance acceptance was established. The authorized extra qualification attempt is exhausted; no automatic retry or landing follows.

Evidence: `.simple/storage/build/phase3-producer-refresh-linkfix/remaining-admission-owner/checkpoint-bridge-20261015/root-launch-corrected.json`, `root-supervisor-checkpoint-owned.env`, and the matrix `verification/logs/compiler_cli_build.log`. A redundant explicit ceiling elevation was refused before any child launch, then removed; the actual run retained the same enforced 8 GiB cap.

The reviewed canonical provenance hook remains an owned working change. Twelve optimization bundles remain ignored drafts pending actual runtime qualification. Recovery C04 now has a direct CLI fixture accepted statically, but its native assertions remain UNRUN. Full compiler/app body-artifact consumption also remains an implementation gap; ABI-only receipts do not authorize code generation. Target `release_phase3` has not been merged or pushed.


## Parallel repair and manual LLVM artifact — 2026-10-15

Three bounded producer repair cycles completed. The final candidate `48a67ecf546f6083283cb4f0d43275bc347c2ef67a4f6fa673ab1a10cd4ead30` reused 1,344 bootstrap objects and compiled four, then linked in 43.7 seconds. This is bootstrap cache evidence, not acceptance of the new pure-Simple object-cache feature. Initializing all eleven MC/DC lowering fields and guarding inactive masks removed the actual verifier SIGSEGV. Cranelift then reported seven successful and four failed receiver modules because enum-backed static initializers were unsupported; its receiver qualification remains failed.

Using the same candidate, LLVM compiled all eleven receiver modules, linked, and passed receiver execution. The subsequent positional route failed before compilation because its helper explicitly requested streaming while MC/DC was enabled. Overall qualification remains failed; LLVM receiver success does not qualify the full Phase 3 inventory or a general test host.

A separate retained-object manual Hello completion passed: 52 ordered object inputs were strictly linked after removing the permissive duplicate-definition flag, and the resulting AArch64 binary executed once with expected output and exit zero. The sole missing entry object was regenerated from the pinned canonical entry-C generator; it was not recovered from the deleted original C file. Receipt: `.simple/storage/build/phase3-producer-refresh-parse-ownerfix-20261015/manual-hello-48a-llvm/attempt/completion/receipt.json`; binary SHA-256 `e22bb6845ab7010d03e86d8fa4da6d41e54d50e836ad5a45fc6a49d11a940a41`. The enclosing 8 GiB/120-second owner exited zero. The original failed manual attempt is preserved separately.

The user subsequently authorized parallel Astra fixes and per-object/manual-link work. Astra owns the Cranelift static-initializer fix; the producer lane owns the streaming/MC/DC route correction and full-object plan, with independent review. New SSpecs, core/MCP checks, full inventory and performance acceptance remain unverified. No target landing or push has occurred.


## Cranelift partial landing requested — 2026-10-15

The user explicitly requested landing the current repairs before continuing. The provider object ABI regression passed one actual test. Both canonical Cranelift receivers compiled, linked and executed successfully; the previously failing four static/global modules emitted real objects, and imported globals retained a single definition with actual importer relocations. MC/DC generated calls now use canonical owner identities; startup probes avoid unconstructed atomic globals. The final producer refresh compiled two units, reused 1,346 and failed zero; this is bootstrap closure evidence, not full Phase 3 inventory qualification.

The mandatory full CLI matrix parsed all 2,679 files, then exceeded the enforced 8 GiB tree RSS limit during HIR at 836/2,679 (peak 8,449,128 KiB; exit 88; quiescent). A separate byte-identical relocated native fixture compiled and linked 12/12 modules but execution crashed. Existing core and disassembly identify a distinct MC/DC token-stack alias: mutating `saved_tokens.push(token)` alters the saved array, so stale tokens leak into excluded functions and generate recursive abort calls. Its repair remains excluded from this landing and will be a separate follow-up. LABEL/counter object binding checks passed; runtime value assertions did not. The original `/test/` fixture collection limitation remains recorded.

Full host, SSpec, MCP smoke, generated doc execution and full Phase 3 acceptance remain incomplete. This is a user-requested partial landing, not STATUS: PASS or a release. Detailed retained evidence: `.simple/storage/build/phase3-cranelift-static-provider-20261015/CAPPED-QUALIFICATION.md`; final source/cache components and all failed/successful receipts are preserved. User subsequently authorized a new bounded repair scope for the token-stack alias bug.


## Token-stack and initializer fixes — partial landing, 2026-10-16

The follow-up repairs use a fresh token-stack container, emit existing MC/DC entry configuration, preserve canonical module initializer exports, and restore documented stable concrete initializer ordering. Independent review accepted all seven source/test pins and eight reporting documents. Actual bootstrap compiled and linked 1,346 selected units with zero failures; sanity, both receiver programs and LLVM planner startup passed. The native 12-module storage fixture passed startup Atomic23, shared values and positive MC/DC recording, with actual single-owner/importer object bindings. These establish narrow native behavior; authored same-lowerer/ordering SSpec assertions remain unexecuted.

The full matrix reached its intentionally configured 60-second deadline (124), so full-host qualification remains incomplete. The separate 413-module compiler regression completed HIR and monomorphization, then reached MIR 64/413 (50 succeeded, 14 failed units) and exceeded the enforced 8 GiB RSS cap (peak 8,392,880 KiB; exit88; quiescent). Diagnostic occurrences include E-MC-ANY001/002 and unresolved-method warnings; these are not counts of independent root causes. The original stale RUNNING controller result is preserved alongside an authoritative terminal assessment. Core/MCP/SSpec/full Phase3 inventory gates have not passed.

Retained evidence: `.simple/storage/build/phase3-mcdc-initializer-export-20261015/FINAL-HANDOFF.md`, `CAPPED-ALIAS-VERIFICATION.json` and `mcdc-token-stack-native-probe/final-failure-summary.json`. Reporting updates are explicitly later than frozen build snapshots. The user instructed landing current repairs first and continuing; the new 2026-10-16 continuation investigates the distinct MIR semantic and memory failures without replaying exhausted unchanged builds. No release or feature-completion PASS is claimed.
