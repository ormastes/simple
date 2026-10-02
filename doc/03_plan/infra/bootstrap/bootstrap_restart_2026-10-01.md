# Bootstrap restart — 2026-10-01

This supplements the [historical Windows restart](windows_bootstrap_restart_2026-09-22.md).
It records incomplete work, not build admission or permission to publish.

## Latest checkpoint: 2026-10-02 cached builds resumed

Provider state checked again: PRs #2156 (SDK links), #2157 (Item5 metadata
tests), #2158 (Item2 transport), #2159 (Item6 warm binding), and #2160 (Item1
follow-up) are now merged. Earlier draft/unlanded descriptions below are
historical. This establishes landing of those slices, not full implementation
or native acceptance of each item. Item3/4 prerequisite gaps and Item7's
remaining profile chain are still open. Memory fix PR #2162 remains a draft
pending native checks; its performance fixture and collector are committed
as `e50bad2c`, with no product-source change after the frozen implementation.

### Memory repair after the 7 GB failure

The user requested fixing the memory bug without introducing performance
regressions and explicitly requested Astra. The scoped source fix is in
draft PR #2162, implementation commit
`0543aa7b69350d396a140d00540c56187813fcd1` on
`fix/bootstrap-memory-retention-20261002`. It publishes complete parent
snapshot authority once, preserves that generation through warm preparation,
and reclaims snapshot materialization scratch after each file. Astra source
review found zero P0/P1 issues. Native allocation, compiler and timing checks
remain pending; this is not a verified memory or performance fix yet.

Validation uses a new selective-on-5831 checkout at
`D:/dev/windows-memory-fix-selective-source-20261002`, preserving the proven
Rust/runtime subtree identities and old caches. The guarded route and baseline
are in `D:/dev/bootstrap-memory-fix-validation-20261002/validation-plan.md`.
The source edit is a new bounded repair; do not restart the unchanged failed
candidate. Keep the 7 GB aggregate limit and 1200-second hello timeout. Only
compiled-and-executed hello success may advance the Phase3/4 route.

The Windows selective candidate source is now frozen at
`6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`, tree
`fab322d37cdeefac46f3b547868fc707aa32ee58`. Materialization completed with
61 links created, zero pending/failed; receipt SHA256 is
`0674217af447de6d04010752c288edbc8b641a90ca54883cfc6271e1e20c56cd`.
The guarded Phase2 rebuild launched as seed PID41912 / exec session90286;
the initial root observation confirmed CPU61.25s and RSS908,976,128B.
This is build activity, not a produced or admitted compiler. Its logs are
under `D:/dev/bootstrap-memory-fix-validation-20261002/phase2/`.
Before hello starts, its wrapper must explicitly override inherited frontend
and HIR cache environment variables with the new producer's private paths;
`--cache-dir` alone does not override those environment variables.

### User-authorized 7 GB Windows attempt

After hello5, the user explicitly changed the cap to 7 GB. The aggregate
Windows Job cap is now 6,835,937 KiB (6,999,999,488 bytes); the 1200-second
timeout, disk guard, worker hint, candidate and cache are unchanged.
Hello6 failed before creating a compiler process because the C supervisor
still rejected limits above 5,859,375 KiB, although its Perl watchdog already
accepted the new limit. Preserve that setup-failure receipt (exit89, root0).

The one-constant supervisor correction is in PR #2161, head
`46ab1b4a1746a181c57ce41ec51a1c92a81e4a0c`. Native boundary checks passed:
6,835,937 KiB admitted a real exit-zero workload; direct helper invocation at
6,835,938 KiB rejected it with exit125. Required structural CI passed. These
checks establish supervisor admission, not compiler or full-bootstrap success.

The actual authorized attempt is hello7, launched with `resume-v11.shs`
(SHA256 `846905e345bca28c05cfa2331ab2f90208ec4009d69dd0933e1a84cf4ea43a45`).
It reuses Phase2 candidate `81500d1a...`, runtime-authority4's pinned snapshot
and hello4's cache. At 2026-10-01 23:26:32 UTC, parent PID34008 was live;
the sampler recorded 658,837,504 bytes aggregate with no child at that sample.
This is a historical live checkpoint, not a terminal receipt. Logs and the
PID/creation-time-bound sampler are under
`D:/dev/bootstrap-phase2-selective-windows/hello7/`. The lane owner must inspect
the terminal guard receipt and compile/run result before advancing. Only a
compiled-and-executed hello PASS enables the authorized Phase3/4 continuation.
Linux and manager retry limits are unchanged by this Windows cap exception.

Hello7 is now terminal: `rss-cap-exceeded`, exit 88, Job peak 6,836,856 KiB
against 6,835,937 KiB, with `quiescent=1`. The last external sample at
23:34:47 UTC recorded parent 2,168,168,448 B and HIR preparation child
4,534,685,696 B; the Job guard caught a higher peak before termination.
No hello executable, compile/run exit receipt or phase-profile output was
produced. Physical D still had 128.519 GiB free. All owned candidate, child
and sampler processes are gone. Preserve hello7's resource receipts and
CSV; this authorized attempt is consumed, and Phase3/4 did not start.

PR #2161 is ready for review, but immediate landing was refused by the
release ruleset: required `SPipe Self Review Admission` is missing. Its
structural check passed. Do not describe it as merged or manufacture the
missing review admission. The ruleset allows merge commits only, and the
repository rejected the attempt to enable automatic merge. The PR is open.

Subsequently, an exact-head Astra high-effort review returned PASS with zero
P0/P1 findings. The canonical SPipe admission workflow run36948315912 passed,
and PR #2161 merged into `release/1.0` at
`b0dc12441573040246e48df294e438b28df6dd38` on 2026-10-02 00:55:54 UTC.
The review is retained at
`D:/dev/bootstrap-phase2-selective-windows/guard-7g-probe/pr2161-astra-review.md`.
This lands the supervisor cap-alignment fix only; hello7 already used the
same tested helper source and failed at its correctly enforced cap. Landing
the fix is not a reason to repeat hello7 or a claim that Phase3/4 is admitted.

### Subsequent recovery: Windows Phase2 linked

Physical D recovered to about 58.97 GiB. The deleted shared Git admin made
the old runtime source worktree unusable; the replacement
`D:/dev/windows-phase2-source-9249-20261001` was verified at exact commit
`9249a1a33d8911d6b797ddcb38ac5c21d4ba7d4b`, tree
`a8f7819080da3200ab0d3059321c08b0d879461f`, with relevant source paths clean.
`resume-v6.shs` changed the runtime-source path and retained the snapshot.

Diagnostic5 PASSED: 2 compiled, 1,115 cached, 0 failed; 79.1s compilation
and 60.6s linking. Candidate `diagnostic5/output/stage2-diagnostic.exe`
is 19,664,384 bytes, SHA256
`81500d1a16010b2fcd911e4a04cc2ada8d9d44dcf5037f1cadb47a1906c92b7d`.
The owned guard completed with child exit 0 and quiescent process tree.
Hello2 failed before compilation because its wrapper sourced the Windows
environment with unset `out` under `set -u`. Preserve that failed receipt;
the corrected hello3 wrapper must reuse this candidate and pinned runtime
snapshot. No Phase3/4 launch is justified until compiled hello executes.

Remote release now includes PR #2154 (item 1/5/7 earlier source slices) and
PR #2155 (manager source integration), at release head `ea15d708abe`.
Later item commit objects were lost with the shared admin and were not
uploaded; their surviving files are being recovered into the independent
`D:/wk-release-items-20261002` checkout. Do not claim those followups landed.
This document was recovered into an independent Git checkout at
`D:/wk-bootstrap-restart-recovered-20261002`, on named branch
`docs/bootstrap-restart-recovery-20261002`, to preserve the restart history.

The hello3 wrapper fixed `out` and pinned the runtime path, then received
the explicit `compile-event-journal-missing` first-build refusal. Hello4
uses the documented `SIMPLE_SCV_INVENTORY_COLD_INIT=1` plus compiler tracing,
under the existing 1200-second timeout and resource guards. It terminated
at the aggregate Job Object RSS cap: peak 5,865,692 KiB versus 5,859,375 KiB,
status `rss-cap-exceeded`, child exit 88, quiescent process tree. Parent
PID35956 and worker PID31052 are gone; no hello executable or compile exit
file was produced. Disk was not the cause (about 102.885 GiB free).
This was the third hello attempt; no further retry is permitted this session.
`resume-v8.shs` SHA256 is
`9069e6d53c997a4075ac1081d3e974fdc31bf0223d15ec1c976ee256847695b7`.
No compiled-and-executed hello PASS has been recorded; Phase3/4 did not launch.
Keep the passing Phase2 candidate, runtime snapshot and all failed hello
receipts. Both Windows and Linux hello lanes have now exhausted their three
bounded attempts; the manager worker lane also remains at its three-attempt
digest-mismatch stop. None of these limits can be reset by renaming a lane
or assigning another agent.

The user subsequently authorized exactly one additional instrumented Windows
attempt, hello5. It reused candidate `81500d1a...` and hello4's cache, with
unchanged 1200-second timeout and 6,000,000,000-byte aggregate cap. It also
failed: Job receipt `rss-cap-exceeded`, exit88, peak5,864,024KiB versus
5,859,375KiB, quiescent1. The last external sample separated parent memory
(2,163,585,024B) from HIR preparation child memory (3,404,926,976B).
That child was `--hir-shard=0/1`; the final hello worker never started. No
phase-profile/HIR snapshot/progress file or hello executable was produced.
The sampler stopped successfully and its CSV is retained under hello5.
This one-attempt exception is consumed; do not launch hello6 automatically.
See `doc/08_tracking/bug/windows_phase2_hello_worker_latency_2026-10-02.md`
for exact evidence and distinctions between confirmed facts and hypotheses.

Recovered Item5 metadata tests are in draft PR #2157, head
`15a0d9c0fbfd651f7d8e64a75047e3f5478d4e17`. Its 17 scenarios require POSIX;
native SSpec and doc generation remain UNRUN. This is not a landed item.

The bounded item recovery handoff now has four separate drafts against
release `ea15d708abe`, with no additional merge:

| Item | Draft PR | Recovered head | Scope |
| --- | --- | --- | --- |
| 1 | #2160 | `c06a99ab8c` | 28 owned SimpleOS source/spec/doc paths |
| 2 | #2158 | `c1c37cef2e` | 3 read-only transport/spec/manual paths |
| 5 | #2157 | `15a0d9c0fb` | 2 metadata spec/manual paths |
| 6 | #2159 | `e05027aff7` | 3 warm-index binding/spec/ledger paths |

Structural CI passed for #2157-2160; this does not replace native
Simple tests, doc generation, Item1 live CLI/guest checks or Item6 performance
evidence. No qualified existing Linux test runner was found in the bounded
runtime audit. The `3eae...` rejected candidate has no passing hello receipt;
the `a6c7...` and `b6c8...` producer binaries cannot substitute as test runners.

Remaining recovery gaps are implementation prerequisites, not verification
alone. Item3's eight-path slice imports absent `collection_site_profile.spl`
and earlier MIR/profile methods. Item7's three-path follow-up depends on the
earlier acc983 HIR/profile implementation; `collection_feedback` does exist
under `10.frontend` and must not be reported absent from a wrong path lookup.
Item4's eleven-path patch cannot apply because release lacks the parent
`macho/macho_link.spl` implementation. Preserve the surviving source snapshots
and exact patch; do not copy unrelated stale compiler files to close these gaps.

### Earlier observations, superseded by the recovery above where applicable

This section supersedes earlier process states. Neither corrected Phase2
candidate has yet compiled and executed hello; Phase3/4 remain unproven.

- Disk recovered externally to 40.54 GiB and guarded builds resumed; later
  samples fell below 31 GiB. Always measure physical free space before launch.
- Linux restored its missing vendor bind and reused the same output/cache.
  Stage2 compiled with 884 reused and 205 rebuilt modules. Candidate SHA
  `3eaeafdd8c7a8ebd27bbdcd6cbfa73484980c3556360b72a55ac357a996658c9`
  is retained as `output-run3/stage2/x86_64-unknown-linux-gnu/simple.rejected`.
  Admission `p2_add` timed out after 180 seconds. Missing sparse
  `release/version.sdn` has now been restored from exact frozen HEAD;
  blob `22fae134107aab28bf1444f33a2023954b97b357`, version `1.0.0-rc.1`.
  This fixes setup only; admission has not been rerun.
  The separate hello probe cleared the missing SCV journal using documented
  cold initialization, then exceeded its RSS cap: 4,724,944 KiB peak against
  4,718,592 KiB, status 88. No hello executable was produced. Retain
  `/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/hello-probe-3eaeafdd-20261002`
  logs/cache; diagnose growth before any further bounded attempt.
  Existing logs contain no compiler-stage markers and the hello cache has
  only empty frontend directories (16 KiB). Supported source tracing is
  `SIMPLE_COMPILER_TRACE=1 SIMPLE_BOOTSTRAP_DIAG=1
  SIMPLE_COMPILER_PHASE_PROFILE=1`; these expose phase/function names and
  `[BOOTSTRAP-PHASE]` timing. Check the three-cycle allowance before any
  further diagnostic execution; tracing does not reset the attempt count.
  Cache producer is `a6c7bb60b8eb9aa777de1edc950d6258b985f5d696a618c598903ad3633b9f8b`,
  not `db712b`. Exact retry details are in
  `D:/dev/linux-bootstrap-manager-abi-value-20261001/linux-phase2-run3-restart-handoff-20261001.md`.
- Windows native-all/backfill passed. Diagnostic4 reused 1,115 modules and
  rebuilt two, then failed on 21 SDK imports: MSVC lacks `propsys` and
  `runtimeobject`. The corrected disk probe then allowed canonical-profile
  native-all to PASS: archive 71,493,616 bytes, SHA256
  `2dff45ba14c7d0c24263c51628a4602e688c8f3ae04909f14f702bb0b5018470`.
  Backfill subsequently PASSED in 1m15s under a measured stage-specific
  26.4 GiB launch gate; the 25.5 GiB live abort remained unchanged. Receipt
  reports child exit 0, quiescent process tree and peak RSS 1,349,636 KiB.
  Backfill SHA256 is
  `76491b9f76fcf92f78f842a79402a34426d50a04c81b66f7ec057f224dc55015`.
  Runtime snapshot is published. Diagnostic5 did not start: D free was
  25.615 GiB, below its unchanged 27 GiB gate. Resume with
  `D:/dev/bootstrap-phase2-selective-windows/resume-v5.shs`; it verifies and
  skips the completed snapshot stages, then uses retained Phase2 caches.
  Script SHA256: `c14bf896ecbbf1b7710addfa56480fb51be929f55fc0704a3e1eeb848086f978`.
  The isolated SDK fix is commit `c80e7406a687` in draft PR #2156,
  rebased onto release `ea15d708abe`; required structural CI passed:
  https://github.com/ormastes/simple/pull/2156 . Representative SDK link
  closure passed; rebuilt driver/full bootstrap remain unverified.
- Generic manager worker smoke failed three bounded attempts, ending with
  `producer/input digest mismatch` despite matching external hashes. No
  worker dispatched. Preserve receipts; startup checks are not job proof.
- PR #2155 remains draft at remote `f7acb23`. Local CI-fix branch reaches
  `8c4328e188bf61810042c817be2d36c78a7df31a`. Review found a P2 owner check
  accepting prototypes instead of definitions. Its three-cycle limit was
  reached; do not bypass it with a newly assigned agent.
- Source-only followups: Item1 `af9506c58731`, Item2 `912c7102de35`, Item3
  `d8f39959f06`, Item5 `33ea00a79e3`, Item6 `3551e65e2bf`/`dc5ae446c934`,
  Item7 `71b21b6785c`. Native tests/docgen/perf remain open. Item4's reviewed
  patch is preserved under `build/item4-signed-reloc-oracle/` in its worktree;
  its existing Git lock and unrelated dirty files were left untouched.
- The old documentation worktree disappeared externally; committed head
  `dad2e30a2cb` remains reachable. This sparse replacement continues on
  `work/bootstrap-restart-checkpoint-20261002`, without pruning old metadata.

## Earlier checkpoint: resource stop and first manager image

This checkpoint supersedes all process states below. Neither host has passed
the Phase2 hello compile-and-execute gate; Phase3/Phase4 completion is unproven.

- Release PR #2153 landed at `fca8bd90dfc1f256ab2252dc0fac83d925389ed8`.
  Exact-head source review and required CI passed. Full native bootstrap on
  this release revision remains unrun. Preserve frozen diagnostic sources and
  caches; a new release run must explicitly pin this revision and its inputs.
- Manager source integration is pushed as draft PR #2155:
  `https://github.com/ormastes/simple/pull/2155`, branch
  `work/release-manager-source-20261001`, head
  `f7acb23dac8c125d65ad9be737c8b27fdad59b22`, tree
  `c3ecbf412ff3a47e30b723cbc971aef76ae46c0e`. The 252-path delta retains the
  release Rust bridge and alias tests. Scoped Astra integration review found
  no P0/P1/P2 defects in inspected merge points; this is not whole-candidate
  or native qualification. The combined tree is unbuilt and PR unmerged.
  CI run `36870973131` failed `local-rt-dual-implementation` for four new
  symbols: `rt_dir_is_real_no_follow`, `rt_shared_parse_cell_read_v1`,
  `rt_snapshot_readonly_nofollow_v1`, and
  `rt_win_profile_path_parents_are_real`. The release integration owner is
  fixing that contract; the other eleven structural rows and bootstrap
  sanity passed. Do not treat the scoped integration review as CI admission.
- Windows diagnostic3 compiled its objects but failed linking 56 runtime
  symbols. The corrective runtime-authority Cargo build reused the private
  debug target and was resource-stopped before completion. Do not start a
  fresh uncached compile or claim a compiler/hello pass.
- Linux `ca19-phase2-diagnostic/output-run3` passed all four Rust build stages
  and preflight, then entered actual Stage2 compilation. Its owned process
  group was stopped when physical D: free space crossed the 25.5 GiB guard.
  Exit 143 is a resource interruption, not evidence of a compiler failure.
  Partial native caches, Cargo artifacts, and logs are retained.
- Phase1 seed `db712b` built the Linux generic bootstrap-builder image from
  source `09a4cbc`: 49 modules linked, build exit 0. Image SHA256 is
  `605995f1c41103ffe92f7bc014e27584c5a1e49d619e1c4cec04f162d0f5a4a4`, at
  `/root/linux-bootstrap-ext4/manager-phase1-db712b-09a4-cranelift-20261001/images/bootstrap-builder-linux`.
  Independent image/hash and retained `--help` exit-0 verification passed.
  Evidence is under `D:/dev/manager-bootstrap-verification-20261001/phase1-owner/cranelift-09a4/`.
  This is not yet a deployed grouped manager or successful job run.
- Independent verification measured the retained build sampler peak at
  210,124 KiB over a 14-second build. This proves neither a performance
  improvement nor full bootstrap memory bounds. Cross-host portable cache
  reuse and process-isolated thread-group completion remain pending.
  The first measured CLI startup took 2.073 ms; four subsequent samples had
  a median of 1.111 ms and peak RSS of 9,404 KiB. These are help-command
  measurements, not a cold-start or comparable compiler-job baseline.
- Grouped keep-going fix `78461c2af21` and stale-marker fix `51eef3b35c4`
  passed source review. V2 markers bind run, inventory, state root and
  manifest. Native worker fault/reap and full-module acceptance remain open.
- Shared-cache trace `3dfa08f3833676a7793964cdadbe13b8da6d55f0` passed source
  review. The witness at `D:/dev/manager-cache-acceptance-20261001/` validates
  decoded payload digests and pinned-root cell paths; synthetic harness
  checks passed. The real shared root remains empty: no cross-host cache
  hit, invalidation, or native-artifact isolation qualification is claimed.
- Physical D: free space was 25.17 GiB at the restart checkpoint. Do not
  restart heavy work below its existing resource guard. Disk investigation
  must preserve reusable caches and unrelated active compiler work.
  D: is ReFS, so NTFS transparent compression is unavailable. A bounded
  cleanup audit found no safe substantial temporary-file reclaim. Deleting
  the fourteen old `D:/VS_Offline.zip.001` through `.014` archives (6.83 GiB)
  requires the user's pending answer; no deletion has been performed.
- An unrelated older Windows direct Phase4 module lane remains diagnostic:
  13,619 inventory entries, 703 passing and 2,879 failing terminal receipts
  at the audit, one pending row. It uses one worker/thread and disabled
  frontend/HIR caches. Historical hello-link evidence does not establish
  executed-hello qualification. Do not count this as managed Phase4 success
  or stop its unidentified owner's processes as part of cache cleanup.

## Historical operational evidence: patched alias runs

This section is superseded by the checkpoint above. Neither host has yet
passed the actual Phase2 hello compile-and-execute gate.

- Windows diagnostic3 uses frozen source `5831e6b3e53f1ac5e8d131d916f97aa3d8c2ffef`.
  Patched producer PID37256 was observed live at CPU 1092.98 seconds and 1117 MiB
  RSS, with empty compiler logs. Outputs remain under
  `D:/dev/bootstrap-phase2-selective-windows/diagnostic3`.
- Linux run3 completed all four Rust Cargo stages, then stopped before any
  pure-Simple stage: `bootstrap_stage3_source_snapshot` reported
  `missing authority root`. The final wrapper verdict names the previous Rust
  stage and does not identify the actual failing operation. Preserve the Rust
  target cache. The missing tracked root is `examples/10_tooling`; all five
  required `src` roots exist. That directory has now been restored at the same
  commit; the focused source-snapshot check passed with SHA256
  `0ac187ff08d57dd22acc0ab7a180ba134de73a24ac0e6219c3a514df449e4050`
  (`alias-output-c542-run3/recheck/source.snapshot`). Do not repeat this passed check.
  Terminal evidence is
  `/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/alias-output-c542-run3/terminal-evidence.txt`,
  SHA256 `0d1c6d3481c03aca7c06aedc15158083300a2b88d8c052c1e1c96df06967f514`.
  The preserved Rust seed SHA256 is
  `11bfc82adceebfad58a6d300c2279401919f882ea292e78fc31beab0d0639a90`.
  The first Linux native alias mini compiled and linked three modules, but its
  executable terminated with SIGSEGV139 before producing output. GDB showed the
  alias resolved correctly, but Cranelift's indirect call treated a raw direct
  function record as a boxed closure. A compiler-side ABI dispatch repair and
  independent review led to the compiler repair below; widening the C closure
  helper alone would retain the wrong hidden-environment/argument ABI. Following
  the actual alias 42/42 pass, full diagnostic Phase2 may proceed while the
  separate typed-call failure is repaired; this does not establish admission.
  The independently reviewed repair is committed as
  `ca19e78c481f8e0b29f8432a4c5fe871f3b7f288`, parent d28, tree
  `efbea4585ae772beca6c8d06a2efa5db915acfb0`. The seed was rebuilt successfully
  in the new source snapshot described below. The reviewed
  preflight-reporting fix `efb5e2c32437fd696fe53798da7d215e258bbda3` is included
  in new source `0ffb3e6132c1fb1bdaee5b41a73e29645b4ac624`, tree
  `661b7cb8f5f6c69a299321ad53f572e5b072b2f2`, at the sibling `ca19-source`.
  The first repaired-seed build stopped at its 4 GiB RSS cap (4252080 KiB peak,
  exit88, quiescent). With 25.32 GiB host memory available, one retry was launched
  using a 4.5 GiB cap, one job, the same source and existing target/vendor cache.
  Its log and start receipt are in sibling `ca19-seed-build-run2`; Cargo PID251
  and rustc PID297 were confirmed live. The failed `ca19-seed-build` evidence is
  preserved separately. The retry passed in 3m52s, peak 4555564 KiB, producing
  seed `db712b47ff4865e0aeea844e3b8e9f2f9b03cba0cce0b9fdc5f078efb85d0b8f`.
  The three-module alias regression passed with exact 42/42 output. The broader
  typed/captured fixture failed at Cranelift verification because imported
  function values had scalar return types. Its independently reviewed source
  repair is `212b913d6e7ea96f4d94305bd668aa5a60406ab5`; native tests are pending.
  Meanwhile the separate diagnostic `ca19-phase2-diagnostic/output-run3` on 0ffb
  completed all four Rust authority builds and preflight 5/5, and launched Stage2
  native compiler PID24263. Source VERSION and the existing vendor bind were
  restored before that attempt; earlier setup failures remain preserved.
- Windows provisional source is separately prepared at
  `D:/dev/windows-provisional-source-8fb-20261001`, exact commit
  `8fb09d215a33c060a69626624a3fedfd5104be15`. The Linux-compatible sparse
  checkout of the same commit/tree is now prepared at
  `/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/grouped-8fb-source`;
  its materialized payload is approximately 290 MiB, excluding vendor/target.
  Its sibling preparation receipt SHA256 is
  `0fb06417f8c71e2440fa18b8621f141790baaa776d6e1d8160216ff96abfbcd8`.
  This source budget does not establish the full output/CAS peak.
  After hello passes, attempt all Phase3/4 inventories without
  waiting for canonical admission, as specified below.
- D had approximately 38 GiB free at the last disk review. The active Windows
  Rust target and reusable outputs were preserved; no cache cleanup was performed.
  Recompute the launcher's source-size budget and 25 GiB reserve before launch.

### Manager deployment and release integration

REQ-BBM-002 requires permitted Phase1-seed manager construction. That attempt
does not depend on a Phase2 hello pass; Phase2 hello still gates Phase3/4 use.
Do not fabricate Phase2 admission for a Phase1-built image. A direct Linux
Phase1 attempt compiled 52 modules, then failed linking Windows-only APIs from
the portable manager. Evidence is retained under
`/root/linux-bootstrap-ext4/manager-phase1-db712b-8fb-cranelift-20261001` and in
`D:/dev/manager-bootstrap-verification-20261001/phase1-owner/`.

The source-reviewed portability fix is `0b0ea9797e487a718b57fd829c28c1135b10d117`.
The launcher memory-cap alignment fix is `e5fa6535d5794551d550c75a744a1bd5d663e54c`.
Shared parse-CAS trace commit `3dfa08f3833` has source review but no bidirectional
native reuse proof. Grouped keep-going commit `78461c2af21` still needs the
reviewed stale-marker/run-identity correction and native fault injection.
The independent three-capability matrix is
`D:/dev/manager-bootstrap-verification-20261001/acceptance-matrix.md`.
No manager image has yet passed native deployment/smoke.

The single-image Phase1 retry has a separately justified 2 GiB disk-growth
budget (prior retained attempt used 5484544 bytes), 3 GiB RSS cap, physical D:
25 GiB reserve and 25.5 GiB running abort threshold. This does not lower the
full provisional route's existing 33 GiB minimum admission guard. WSL virtual
filesystem capacity is not physical D: capacity.

Release PR #2153 contains the selective alias/Windows-runtime/preflight fixes;
its high-effort source review found a builtin-looking alias edge case, which
must be corrected before merge. Draft #2154 holds the separate 72-path item
1/5/7 source snapshot with unrun native gates. Neither is release qualification.
Manager release integration requires the reviewed dependency-closure candidate
in `D:/dev/manager-release-prerequisite-closure-20261001.md` (256 paths), not just
the 43-path incremental patch. Preserve release's Rust bootstrap runtime bridge
through a source merge; do not overwrite release with the frozen manager tree.

## Historical initial evidence

Both hosts used frozen source `bf28063b843526d1212a760deaed623367a569e5`.
Neither has an admitted Phase 2 compiler from this source.

| Host | Result | Preserved evidence |
| --- | --- | --- |
| Windows | 1,089 modules compiled, link succeeded; canonical HIR shard sanity failed with exit -1. Spawn/wait failure is possible; an OS crash is not established. | `D:/dev/bootstrap-release-rebased-20261001-windows/attempt3/result.json` and its output tree |
| Linux | 1,089 modules lowered; retry 6 reused 1,087 objects and failed linking `rt_process_spawn_async_value`. | `D:/dev/linux-bootstrap-manager-abi-value-20261001/bootstrap-output-release-bf28063-phase2-run3` and adjacent run6 log |

The Windows linked candidate SHA256 is
`cd618d3cd691fefca4f073365dea54e9174d277d835feaf825ea995ef256e0de`.
It is diagnostic evidence, not an admitted tooling runtime.

The missing Linux export belongs to the Rust static archive: archive inspection
identified Rust codegen-unit members. Its build intentionally excludes
`runtime_native.c`, where the C value adapter already exists. Repair therefore
requires the Rust provider's two-word value facade and matching caller/registry
wiring, rather than copying the C adapter into an unrelated translation unit.
The raw three-operand process ABI must remain distinct.

The isolated Linux C-provider harness passed actual child argv delivery
(including spaces, quotes and an empty argument), tagged/raw commands, wait
exit 37, and missing-command refusal. Evidence:
`D:/wk-bootstrap-spawn-value-abi-20261001/build/native_probe/process-spawn-value-abi/c-provider.log`.
This does not test the repaired Rust archive, establish Windows parity, or admit
the Phase2 compiler. Those gates remain open.

The source-reviewed ABI candidate is
`19adbef88f2c149fb8081d6f7e373e1115a281e0` (tree
`9bb7571538378b4920231d365580ad7d32ecc4a4`). It adds the Rust export and
two-operand registrations, corrects `io_runtime` to call the value facade, and
includes a guarded native fixture. Earlier C logs predate the final fixture
revision; exact-candidate provider execution is still required.

Windows native testing exposed a separate ownership mismatch: legacy
`_spawnvp(_P_NOWAIT, ...)` returns a handle, whereas `rt_process_wait` requires
a child recorded in the runtime process registry. The test spawned a child but
wait returned -1. Evidence is retained at
`D:/dev/bootstrap-spawn-value-windows-test-20261001/`. Keep Windows restart
held for that repair. Linux provider qualification and its subsequent isolated
bootstrap can proceed independently if no shared-source impact is found.

### Corrected-source handoff

The final reviewed repair revision is
`9e89f101c5028d67e9796b7333a64762625be0c5`, tree
`6e7578e67084e2ad0c039c95edd81884b2f9b21e`, on named branch
`fix/bootstrap-spawn-value-abi-20261001`. It retains Windows children by PID
in the existing wait owner, including timeout/re-wait/reap behavior.
Windows C-provider testing passed with exact fixture and four source hashes;
independent review matched those hashes. Linux C-provider testing also passed.
The first repaired Rust staticlib build succeeded and exports both raw and
value symbols; final-revision archive/harness qualification remains separate.

Windows attempt4 is authorized to create a fresh source snapshot and run the
canonical Phase2 build at this revision after resource and source checks.
Linux is authorized to retry the same revision after its final provider
qualification. This supersedes the Windows repair hold above; it does not
promote release/main, admit Phase2, or establish Phase3/4 completion.

Windows attempt4 started at 08:51 UTC on 2026-10-01 (launcher PID 33708),
using `D:/dev/windows-release-corrected-source-20261001`; startup materialization
is not compiler admission. Freeze, validation and start receipts are under
`D:/dev/bootstrap-release-rebased-20261001-windows/attempt4/`.
Linux final-revision build, one focused Rust test, and the linked archive
harness passed; receipt:
`D:/dev/linux-bootstrap-manager-abi-value-20261001/linux-abi-fix-validation-9e89.receipt.txt`.
PR #2148 was updated to this revision and remains open; release was not merged.

### Live retries and manager source boundary

Windows attempt4 has passed the Rust seed build and is building Rust native
support (launcher PID 33708, Cargo PID 4332 at observation). Linux's corrected
literal-script launch reached Cargo PID 4236, compiling the Rust seed with two
jobs. Its start receipt and log are respectively
`D:/dev/linux-bootstrap-manager-abi-value-20261001/linux-bootstrap-9e89-run1.start.txt`
and `linux-bootstrap-9e89-run1.log` in the same directory. The earlier session
77090 failed before launch because nested shell expansion corrupted a mount
path; it is not a running build. The replacement uses session 99962 with the
Rust target and Stage3 authority subtree bound to D-backed WSL ext4 in the
same invocation. Neither retry has admitted Phase2 yet.

Windows subsequently passed bootstrap preflight and entered the actual
`stage2-native-build.log` command. That log explicitly reports the Rust seed
does not implement dynload and emits a single native artifact instead.
Record this Phase2 build as one-binary; it proves neither dynload nor managed
module support. Linux completed the Cargo backfill invocation and remains
in post-build provenance work. These milestones do not imply admission.

The frozen legacy script's `--resume-stage4-from-admitted` requires Phase3
provenance. It therefore cannot satisfy the requested independent
Phase2-to-Phase4 build. Stop after Phase2 with the typed Stage3 receipt;
continue legitimate Phase3 work while the grouped manager is qualified.
Do not count legacy Phase3-produced Phase4 as fulfilling that requirement.

The grouped manager source is newer than repair revision `9e89f101c502`.
Its current handoff checks the admitted Phase2 source snapshot byte-for-byte
before building eight manager/authority images. An admission from the repair
revision cannot be relabeled as admission of the manager revision. Freeze the
integrated manager source and satisfy its actual producer/source contract
before using RUN-4 for independent Phase3 and Phase4 dispatch. Static checks
of that path remain distinct from native qualification.

The enforcing entrypoint is `scripts/bootstrap/prepare-phase2-build-manager.shs`:
it reads the admitted `source_snapshot_path` and `source_snapshot_sha256`,
uses the canonical snapshotter on the selected source root, and refuses a
different snapshot before image construction. Preserve this check. A new
matching Stage2 admission is required by the current implementation; compiling
newer manager source diagnostically with an older admitted compiler does not
satisfy that admission. Schedule the new frozen-source build within each
host's memory budget after the current run reaches its handoff, keeping the
current run's artifacts and caches intact.

Root review found an additional pre-freeze scope gap at grouped revision
`0c4de9d3b85`: `bootstrap-phase4-grouped.shs` dispatches both module backends,
but `build_binary` hardcodes `--backend llvm`. That does not fulfill Phase4
binary and module builds for both LLVM and Cranelift. The script owner must
parameterize binary backend selection, isolate backend output/cache/state,
and require both binary sets in completion verification. A missing or
tampered Cranelift binary must prevent completion. Script candidate
`ce228c9ae75` now parameterizes the actual compiler backend, isolates binary
paths and task IDs, and requires twelve binary outputs/receipts (five Phase4
binaries and one Phase3 binary, each for both backends). Root reviewed the
dispatch change; the script owner's focused missing/tampered-Cranelift fixture
passed. Integration and native qualification remain separate gates; a
modules-only backend PASS is insufficient.

The initial-to-managed continuation also needs repair before freeze. The
trust-root command requires `--stop-after-stage2` and exits before RUN-4;
`--resume-stage3-from-admitted` executes the legacy Stage3 script before it
can reach RUN-4. A recipe with an unspecified planner receipt does not close
this gap. The script owner is implementing an explicit admitted-Stage2
managed continuation that retains canonical planner, producer and complete
source-snapshot checks without rebuilding an already admitted Stage2.

### Manager candidate now frozen

The repaired manager candidate is frozen on
`work/grouped-native-release-20261001` at
`018ed390eb7131a56f7e4d5d10f96a724765a325`, tree
`fec3204bd000fc525dfb89e73a65374b50f5985c`.
The host recipe and static-evidence limits are recorded in
`D:/dev/grouped-compile-release-audit-20261001/source-freeze-018ed390eb71.md`
(SHA256 `dcd00994ebf178190d292a9a1d0c4dad45d9eaaeeb2337685e6b836bbe238e92`).
This supersedes the pending source-repair notes above, not their native gates.

The initial trust-root run uses `--full-bootstrap --stop-after-stage2`
and `--produce-managed-receipt=self-host-convergence-check`. The subsequent
`--resume-managed-from-admitted` route consumes the emitted Stage4 planner
receipt, verifies both canonical Phase2 copies against exact admission,
requires the compiler-test PASS evidence, and enters the shared manager
handoff. Both backend binary sets and all four module/index lanes are required.
No admitted Phase2 or native completion exists for this new source yet.

The shared parser-cache directory is provisioned as the same physical path:
Windows `D:/dev/simple-shared-parse-cas-v1`, WSL
`/mnt/d/dev/simple-shared-parse-cas-v1`. Cross-platform hits remain unverified.
Both bootstrap owners are preparing new isolated sources when I/O permits;
no competing compiler is launched on the same host. Linux's current Git
alternate-object warning is nonterminal at observation; preserve its live
metadata, and use isolated portable Git metadata for the future ext4 checkout.

### Windows attempt4 terminal result

Attempt4 compiled 1,089 modules (zero reused, zero failed) and linked a
19,251,712-byte Phase2 candidate with SHA256
`c5203b45498d18caab9568a59a19516380973fff33a9292918a82afa1e01fb2d`.
Compilation took 1391.1 seconds and linking 55.6 seconds. It then failed
canonical `p2_add` frontend sanity: raw status 126, HIR worker access
violation `-1073741819` (`0xC0000005`), claimed/sealed zero and no finished
inventory. The bootstrap launcher exited 2. No Phase2 admission or Phase3
result was produced.

Evidence is `attempt4/exit-code.txt` and
`attempt4/output/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-failure.log`
under `D:/dev/bootstrap-release-rebased-20261001-windows/`.
This is a concrete worker crash, distinct from the earlier wait status -1.
The focused spawn/wait ABI fixtures passed; they do not establish the cause
of this new fault. `bootstrap_spawn_abi_fix` owns Astra diagnosis in a new
isolated worktree based on manager revision `018ed390eb71`. Preserve both
frozen sources, the failed candidate and caches. Do not repeat the same
full build before diagnosing the failure.

## Repair and restart

1. Repair process-spawn ABI parity in an isolated branch from the frozen base.
   Identify the actual linked archive provider and calling convention on each
   host; a same-named raw export does not establish value-ABI compatibility.
   Independently review the fix and run focused native adapter tests before
   selecting a new immutable source revision.
2. Preserve old source, logs, candidates and native caches. Reuse objects only
   when canonical producer/source/ABI keys admit them; do not relabel old
   cache entries for the new revision. Never run concurrent writers in one cache.
3. Linux requires D-backed WSL ext4 bindings for both the Rust authority target
   and Stage3 authority subtree, maintained in the same live WSL invocation.
   Preserve failed authority trees. Installed prerequisites now include `file`,
   `libsqlite3-dev`, `zlib1g-dev` and `libzstd-dev`.
4. Restart canonical Phase2 builds with `SIMPLE_NO_STUB_FALLBACK=1`, separate
   host outputs and fresh resource checks. Do not blindly reuse the historical
   twelve-worker command. Record exact source SHA, command, producer hash,
   cache scope, terminal verdict and canonical admission receipt.
5. Once admitted, use Phase2 to build and verify manager images and non-vacuous
   tooling. Specs require actual executed assertions and result counts.
   Rust seed and linked-only candidates do not qualify as test runtimes.
6. Build Phase3 and Phase4 independently from the same admitted Phase2, with
   phase/backend-specific caches. This supersedes the historical Phase4 wait
   on Phase3. LLVM precedes Cranelift within each requested backend sequence.
   Phase3 must complete MIR generation and validation for its full required
   inventory, then continue through the remaining build outputs. A planner
   receipt, semantic-index MIR, or partial MIR sweep is not Phase3 completion.
   Frozen legacy scripts may have a different dependency graph; do not claim
   they provide this independence until the updated manager path is verified.
7. Adopt each independently verified manager feature into the bootstrap source
   freeze. Continue permitted legacy bootstrap work while manager qualification
   is pending. Require full requested binaries and module inventory, typed
   target outcomes, actual resource enforcement, and both phase verdicts before
   reporting completion. Static checks alone do not prove this boundary.

## Ownership and stop conditions

### User-authorized provisional progression (2026-10-01)

Current Windows diagnostic Phase2 source is
`5831e6b3e53f1ac5e8d131d916f97aa3d8c2ffef`, tree
`22afae5df9e23ae5809d16fde878ead53d29c9e5`, at
`D:/dev/windows-phase2-source-selective-20261001`: 9249 plus only the reviewed
CAS return-type closing-bracket correction (52eb). Materialization and native
consumer validation passed. Actual compiler PID 37256 started under launcher
33572, one LLVM worker with 6 GiB budget, using patched seed d78267. Private
logs/cache/output are under `D:/dev/bootstrap-phase2-selective-windows/diagnostic3`.
This is noncanonical diagnostic compilation, with no Phase2 admission or hello
success yet. Diagnostic1's cross-volume temporary publication failed before
compilation; diagnostic2 reached and exposed the corrected CAS syntax error.

Linux selective source is frozen at
`d28b1542af6b1f0d763dd63cb8021b5c12f1faed`, tree
`55d7cde8b7c0656905de1c086c300705c846e2c2`, at
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/alias-source`. Helpers are now
materialized. Canonical run3 is live rebuilding the patched Rust seed with one
job, Cranelift, a 4 GiB RSS budget, a copied 273 MiB target cache, and physical
`LLVM_CONFIG=/usr/lib/llvm-19/bin/llvm-config`. Observed handles: shell 3865,
Cargo 7660, rustc 8017. Start receipt and log are under
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/alias-output-c542-run3`.
Original 9e89 outputs and crash evidence remain preserved. Neither host has
begun Phase3/4.

The integrated diagnostic manager is frozen clean at
`8fb09d215a33c060a69626624a3fedfd5104be15`, tree
`d1e0069cda6774469b6696b6f333c27f85a91929`, in
`D:/wk-grouped-provisional-authority-20261001` on named branch
`work/grouped-provisional-integrated-20261001`. The selective 43-file manifest
and launcher arguments are in `D:/dev/grouped-provisional-route-review-20261001.md`.
It includes index retention/pruning corrections, failed-only image reuse and
sampled process-tree RSS/timeout enforcement (not a kernel allocation cap).
Script scheduling/retry fixtures passed; no native manager run is proved.
The route accepts any candidate that actually builds/runs hello against the
pinned source, with producer/source lineage explicitly unproven. It does not
require rebuilding the producer after manager-only changes. Its final receipt
is diagnostic INCOMPLETE, never canonical admission or release completion.

Remote merge checkpoint: `release/1.0` is
`8ef1333185b3578908a3b5499231859dfd865899`, containing prerequisite PR #2148.
Items 5, 7 and 1 (#2149, #2150 and #2151) were merged into
`work/bootstrap-main-fixes-20261001`, now
`8425a5339888f269681a14be41d5f27ec866ebb8`; those three topic merges are not
ancestors of that release head. Merged PR state therefore does not establish
release placement or executable verification. Keep active bootstrap freezes
unchanged and use new follow-up PRs for additional tests.

Latest observed checkpoint: the Windows provisional hello attempt under
`D:/dev/bootstrap-phase2-provisional-windows-20261001/hello1` failed compilation
with HIR worker `0xC0000005`, zero claimed/sealed modules, and no executable.
Producer SHA starts `c5203b`; this does not satisfy the provisional gate.
The isolated alias fix is `c542bd96846a5092008f47493ca0e599ef126a93`;
focused Windows Cargo tests passed: 3 tests, 0 failures, including native alias
owner/function-value collisions and non-native alias preservation. Evidence:
`D:/dev/bootstrap-hir-alias-windows-test-20261001/cargo-test.stdout.log` and
`result.json`. This proves the focused seed regressions, not a passing Phase2
or full module build. Separate Windows C declaration
fix `993bb1d6c1a513a1424aa03d2e45dd8226cb014d` passed focused clang-cl syntax
compilation and needs adoption into a new combined source revision.

Combined source is now frozen clean at
`9249a1a33d8911d6b797ddcb38ac5c21d4ba7d4b` (tree
`a8f7819080da3200ab0d3059321c08b0d879461f`), including the alias and C fixes.
Patched Windows driver build initially started as PID 35156, then was stopped
before compiler/driver artifacts because it lacked the required LLVM feature.
Corrected PID 26896 runs `cargo build -p simple-driver --bin simple --features
llvm --jobs 1` with the same private target and no concurrent Cargo writer.
Logs are `driver-build-llvm.stdout.log` and `driver-build-llvm.stderr.log` under
the alias test evidence directory above; `driver-build-correction.json` retains
the reason and original process identities.
The LLVM build required restoring tracked `tools/counterpart` files omitted by
sparse checkout; no source content changed. Retry PID 33012 completed in 4m54s.
Patched driver SHA256 is
`d78267bd8de91836ef9232e908d33b764ce4121115ef1124a5e0c039c5d679a0`.
The native collision fixture now PASSES: all three modules compiled (zero cache
hits/failures), executable exit 0, output 42 twice. Prior baseline output was
-30 twice. Evidence: `D:/dev/bootstrap-hir-av-20261001/alias-patched/result.json`.
This is readiness for corrected bootstrap, not Phase2 admission. D free space
was about 27.8 GiB; reserve remains 25 GiB pending safe owned-temp reclamation.

Linux Stage2 compilation/link completed: 1089 compiled, zero reused/failed,
1753.9s compilation plus 47.0s link. The canonical run then failed admission:
Windows-style Git worktree metadata cannot be resolved inside WSL, yielding
`SCV-E-ADMISSION: git-event-source-unavailable` during `p2_add` smoke.
Preserved candidate is
`/mnt/d/dev/linux-bootstrap-manager-abi-value-20261001/bootstrap-output-linux-9e89-run1/stage2/x86_64-unknown-linux-gnu/simple.rejected`.
The user-authorized provisional hello compile/run is still required before
starting its Phase3/Phase4 lanes; linked output alone is insufficient.

Linux provisional hello was attempted in a tiny ext4 Git project with documented
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`. HIR aggregation crashed with exit -139,
zero claimed/sealed modules and no executable. A bounded six-second GDB capture
confirmed `AssocTypeResolver_dot_normalize+338`, called from
`source_authority.compiler_source_authority_inventory_roots_v1`, dereferencing
null (`r11=0`). This establishes the same alias defect fixed by c542, rather
than merely inferring it from similar crash symptoms. Candidate SHA256:
`fae51dca60932505b20d08724fa97244e5cbca900814c28c87a3568ce6871190`.
Evidence: `/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/hello-probe/debug/gdb.log`.
The selective Linux fix is being prepared on an isolated source with the prior
Cargo target reused through Cargo's normal invalidation; original 9e89 is retained.

The user explicitly requested starting next phases without full admission when
the Phase2 candidate can build hello world. This supersedes the admission wait
above for diagnostic execution only. On each host, compile a real hello-world
program with the candidate and execute the resulting binary; record the exact
producer hash, command, exit status and expected output. A successful version
query or interpreted source run does not establish this gate.

After that smoke passes, start feasible Phase3 full-MIR and Phase4 binary/module
builds independently using Phase2, in separate provisional outputs and compatible
phase/backend caches. Attempt the complete required module inventories, not a
sample subset, using keep-going for independent failures where supported. Record
each failed module and continue unaffected work through the end; run LLVM then
Cranelift within each lane. Continue formal admission and compiler fixes in parallel.
Use supported diagnostic routes or legacy direct phase commands where manager
admission is unavailable; never forge an admission receipt. Provisional progress
does not establish release qualification or verified completion. Windows and
Linux lane owners own their respective smoke and subsequent diagnostic runs.

`bootstrap_spawn_abi_fix` owns the isolated ABI repair; `item5_astra_impl`
provides independent review; `linux_bootstrap_resume` owns the Linux retry.
`grouped_compile_audit` owns manager integration in its separate feature tree.
The root serializes source freeze/integration and Windows restart ownership.

At most three fix/verify cycles per concrete failure; never repeat green
checks without a new change or unresolved concern. Report a remaining failure
with durable evidence instead of spinning or weakening admission.

### 2026-10-02 Windows four-worker memory-fix validation

Selective memory repair uses commit `6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`
(tree `fab322d37cdeefac46f3b547868fc707aa32ee58`) in
`D:/dev/windows-memory-fix-selective-source-20261002`.
The initial single-worker job was intentionally interrupted for the requested
parallelism: exit 143, guard status `interrupted`, Job `quiescent=1`.
All 191 completed object files and original logs/receipts were preserved.
This was a concurrency reconfiguration, not a compiler failure.

The replacement uses the same producer, source, runtime and object cache with
separate logs/output under `D:/dev/bootstrap-memory-fix-validation-20261002/phase2-parallel4`.
Its stderr confirms four effective LLVM workers; seed PID 18120 was created
at 10:48:34 KST, exec session 29138. The 7GB process-tree cap and D: disk guard
remain enforced. Objects increased from 191 to 265 at the first checkpoint;
a subsequent live process sample showed CPU 886.625 seconds and RSS 1.22 GiB.
These observations establish active compilation, not a completed candidate.
The candidate, compiled-and-executed hello gate, Phase3 and Phase4 remain pending.
Reconfiguration evidence is `phase2-parallel4/reconfiguration.env`.
Resume-v2 SHA256: `9cf6c30452b0baed014d67d82af3f739d794843833c2d95b3202983341912ec8`.

Linux has the same clean selective source and pinned SPipe submodule prepared.
Its owner is launching a four-worker guarded build; no live compiler PID has
been confirmed at this checkpoint. Manager producer-binding investigation has
resumed separately; no unchanged dispatch retry or manager acceptance is claimed.

Linux launch subsequently confirmed live by `ps`: PID 244, exec session 15229,
47 seconds elapsed, CPU 169%, RSS 1,028,280 KiB at the first root observation.
This Phase2 seed build uses Cranelift, requested `--threads 4`, the exact 6b9
source, and `core-c-bootstrap` from that checkout's `src/runtime`.
The seed reports that `dynload` emits one native artifact; this is not evidence
of a completed module build. Source/cache/log/output root:
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/memoryfix-source-6b9edd328`.
Log: `build/native_probe/stage2.log`; resource receipt:
`build/native_probe/stage2.rss.env`; cache: `build/bootstrap/native_cache`.
Aggregate RSS guard is 4,718,592 KiB. Physical D: free space is 122.89 GiB,
independent of WSL's apparent 932 GiB free. Effective worker-count diagnostics
and terminal results remain pending. Phase3/4 still require the real hello gate.

### 2026-10-02 Linux object completion and handoff review

The exact-6b9 Debian Phase2 attempt reached `compiled=1118 reused=0 failed=0`,
then failed at link with missing `rt_dir_is_real_no_follow`,
`rt_shared_parse_cell_read_v1`, and `spl_thread_current_id`. No Phase2 producer
or hello executable was produced. Guard receipt reports exit1, quiescent1,
peak1,850,480KiB against4,718,592KiB. Retained objects:
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/memoryfix-source-6b9edd328/build/bootstrap/native-objects-IhVRke`.
The Linux owner is repairing actual runtime linking with the1118-object cache
preserved. This supersedes the earlier live-PID244 checkpoint.

The cross-host audit is saved at
`D:/dev/bootstrap-crosshost-apply-verify-20261002/evidence-matrix.md`.
It found prelaunch handoff defects, including Linux hello/producer binding,
cache isolation and module coverage, and a Windows manager-only gate without
the authorized direct fallback. Owners are repairing launchers before execution.
Calling a bootstrap_main native build Phase3 MIR is insufficient: full inventory
and actual MIR-pipeline evidence are required. Manager dispatch is still unproven;
three corrected setup attempts ended before worker execution. Native diagnostic
work is pending; no admission check was waived.

User requested more cores. Next substantive builds target8 workers per host
under unchanged memory/disk guards. Windows remains at4 for the current compile:
810 objects had already been cached when the request arrived, so replaying its
frontend was judged slower than finishing. Direct measurement previously showed
3.99 active Windows cores and Linux386% averageCPU, establishing actual parallel
execution but not absence of a performance regression. Phase3/4 have not started.

### 2026-10-02 Windows Phase2 linked; first real hello running

Windows exact6b9 candidate build succeeded:927 compiled,191 cached,0 failed;
compile1708.8s,link54.0s,total1762.7s. Candidate:
`D:/dev/bootstrap-memory-fix-validation-20261002/phase2-parallel4/output/stage2-fixed.exe`,
19,666,432bytes, SHA256
`e7ec89c1f106353cc8fdc792d5d41359336c72287f410aa039b57d8f6101dfdf`
(independently hashed by root). Guard complete/quiescent1,
peak1,886,248KiB. This proves linking, not self-hosted hello or full bootstrap.

The automatic hello1 wrapper failed before compiler launch because a nested
script retained the previous output path. That setup evidence is preserved.
Fresh hello2 launched at11:19:40KST with producerPID41040, Job guardPID40344,
monitorPID7432, execsession29550. It pins the candidate hash and uses private
SIMPLE_CACHE/frontend/HIR, cold-init1, one worker,7GB guard,1200s timeout.
The single-worker cold hello preserves comparison with the prior memory failure;
next substantive Phase3/4 builds target8workers. No hello completion is claimed.

PR2162 was merged by another session into release/1.0 at02:03:28UTC,
commit3d021ee9bc6456857a1450928fd6aff127aba13f. This supersedes earlier draft
status but does not establish native verification. Manager diagnostics are in
draft PR2163, release-based headd55ff8ea217875082f077d0455cc49720b5bfbc5;
worker dispatch remains unproven.

Linux cached retry subsequently launched with8workers, compilerPID253 and
watchdogPID246. Runtime provider archive SHA256
`786a6f3914451356a406340a9ee6e680c8a588fa919af34f815b9ae1ed088a1a`
is selected via explicit runtime-authority/runtime path. It records2compiled,
1116reused,0failed and is linking; no terminal verdict yet. Log and receipt:
`build/native_probe/stage2-retry8.log` and `stage2-retry8.rss.env` under the
same6b9 Debian checkout. Original failed runtime/link evidence is preserved.

### 2026-10-02 guarded native failures and branch candidate

Windows hello2 terminated before producing an executable: parse1/1 reached
HIR preparation, whose diagnostic sink failed with
`SIMPLE_MEM_SNAPSHOT_FILE could not be established safely`. Job exit1,
quiescent1,peak3,500,324KiB: the7GB memory cap was not hit. A direct C probe
of the exact runtime function on the same D: parent succeeded (handle204,
closePASS); an independent Simple call-boundary investigation is assigned.
A changed hello3 setup may omit only that optional internal sink while retaining
external Job/RSS sampling and the same candidate/cache; no success is implied.

Linux stopped after3native attempts, all at link and below its RSS cap.
Initial attempt missed3providers; retry8 missed rt_string_new; retry8-final
selected the provider-only archive as complete native-all authority and missed
broad core runtime symbols. Both partial archives are invalid runtime authorities.
Audit: D:/dev/linux-memory-fix-validation-20261002/linux-native-validation-final.md,
SHA25648ad48155ac2b498a5bfc34eb627e6b0ee703db9cd8cbfa75c1a1b90044384ae.
No Linux hello or Phase3/4 execution occurred. Complete runtime-bundle repair
remains outstanding; do not repeat the partial-archive attempt.

Requested main-on-release rebase completed in an isolated worktree. All133
nonmerge main commits are exact equivalents or reviewed adaptations already
on release;38merge commits showed no separate resolution delta. Candidate is
exactly3d021ee9bc6456857a1450928fd6aff127aba13f. Remote named originals and
work/main-on-release-20261002 preserve evidence. Public main remains unchanged:
GitHub rules allow existing admin bypass only through PRs. User choice about a
temporary actor-specific bypass change is pending; elapsed time is not approval.

### 2026-10-02 hello gate and independent phase attempts

Windows hello3 is PASS: compile.exit-code.txt=0, run.exit-code.txt=0,
run.stdout.log=`hello`, under
D:/dev/bootstrap-memory-fix-validation-20261002/hello3. The producer is the
same e7ec89c1f106353cc8fdc792d5d41359336c72287f410aa039b57d8f6101dfdf
candidate. Only the optional SIMPLE_MEM_SNAPSHOT_FILE sink was disabled;
external Job/RSS enforcement remained enabled. Peak Job commit was
5,130,432KiB. This is a hello gate, not full bootstrap or diagnostic-sink PASS.

Independent Phase3 and Phase4 attempts use frozen source ba066da503e50a386294e27f9e09ecbd27373add.
Phase3 LLVM bootstrap and Phase4 LLVM bootstrap both hit the 7GB Job cap
(exit88). The first loader module also exceeded that cap with one compiler.
Do not repeat unchanged binary attempts or count resource termination as PASS.
Phase4 interpreter closure failed at missing std.args. A release-based isolated
agent is replacing that import with the existing argument facade for both hosts.

The Windows module collector is being corrected to guard each compiler
individually, allowing a contained failure row before trying the next module.
Nested Jobs were rejected by the helper; the coordinator now stays outside
compiler Jobs. Deep receipt paths also exceeded the helper MAX_PATH limit;
receipts now use D:/dev/bootstrap-module-jobs-20261002. The v5 Phase3 first
module was reported launched as PID40880; this is historical launch evidence,
not a persistent liveness claim. All previous attempts and caches are retained.

Linux Astra repair found the initial run selected a complete seed native-all
archive, not merely generated core C. Preserve that corrected diagnosis alongside
the earlier failure audit. Full original authority SHA256
4cde5db743726158a0f4c9de7e5153c969ff5165ba0d0301ba2343c6e47197eb
plus three isolated current C providers yields SHA256
d0c9cd0be5ad8635868289de61acaebc526213d92044b684608c64df2f3675bd.
All 43,782 original export names/counts remain; exactly three exports are added.
Root reviewed provider symbols and nonempty relocations: no duplicate allocator
or private runtime state. Evidence:
D:/dev/linux-runtime-binding-20261002/provider-audit.json.
Native validation is authorized after the behavioral harness; success remains
unproven. The Linux downstream launcher is prepared for independent Phase3/4,
LLVM then Cranelift, fourteen binary jobs and four complete module inventories.
A single producer hello receipt should be shared across the two coordinators.

Draft PR2164 contains the shared snapshot semantic-text ABI correction;
PR2163 contains manager admission diagnostics. Neither draft proves native
acceptance or manager dispatch. Direct guarded scripts remain the active route
until the manager actually passes admission/worker execution. Common source
fixes must be reviewed on release and applied to new frozen host lanes, never
mutated beneath an active build.

### 2026-10-02 Linux self-hosted hello PASS and Windows continuation

Linux repaired Stage2 is now linked and guard-complete (exit0, quiescent1,
RSS enforcement enabled): 2compiled,1116cached,0failed;50.2seconds total.
Producer SHA25604d72b6adc0e9d1b6696f721bb4a088b5194f10d80642f0e43c2cdabb6c5444d.
The bootstrap seed explicitly skipped unsupported dynload and emitted one binary;
this does not verify dynload. Actual self-hosted LLVM hello compilation and
execution passed, printing Hello World. Receipt:
/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/linux-runtime-binding-20261002/hello-gate.json
SHA256453323b23cce7dda3c97b4f22d9ea81dbdfe85bee5ddf142a33b37e858eb6ea2.
Derived ELF SHA25697a8ea0f75b262f8e55a8a3538616dab532496867b1ca4a3b299aa284f926537.
Root read the pinned receipt; Astra verified the terminal guards. Stage2 peak
1,910,628KiB; hello compile247,268KiB; hello run8,264KiB. The initial broad
project hello invocation failed inventory admission and remains recorded.

Linux launcher142e46db0d5fc280db5bfa15e831d0045e8b27eaa935c1cf93070a477dda7b6d
has root review for parallel Phase3/4 after memory admission. It reuses the exact
hello gate rather than compiling it again in each phase. Launch authorization
is not evidence that those phase jobs have started or passed.

Windows per-module keep-going is proven: the capped loader __init__ attempt
recorded a failed row and the collector advanced to subsequent modules in both
independent phase lanes. Subsequent real errors include unresolved wildcard
bindings in aspect_pack_io.spl and unresolved atomic methods in
aspect_lifecycle_gate.spl; a separate triage owner is investigating. No inventory
seal or full-module PASS exists yet. Shared interpreter facade fix6fad4592 is
in draft PR2165 with static review accepted and native validation pending.

### 2026-10-02 Linux full-route admission correction

The first parallel Linux route d244a6e did launch coordinator199 and children
273/274, but task logs exposed SCV-E-ADMISSION compile-event-journal-missing.
It was stopped through its owned signal handlers; all46attempted guard receipts
are quiescent and no owned process remains. Evidence:
D:/dev/linux-runtime-binding-20261002/route-stop-audit.json.
No module PASS is claimed from this attempt. Existing output/caches are kept.

Source inspection corrected the initial assumption about private caches:
SIMPLE_CACHE does not relocate admitted SCV inventory; it lives at checkout
build/scv. The revised launcher must serialize one cold initialization, prove
admission, and let both phase lanes reuse that checkout journal with cold-init
explicitly disabled. Any subsequent SCV-E-ADMISSION error must stop the route,
not repeat the same configuration error for every module. This change is pending
review/native probe and is not yet a successful full-route restart.

Manager ABI fix78ef897a0b is committed on its isolated branch: the no-follow
directory predicate was absent from text-argument registries/runtime declarations.
Its compiled wrapper passed one tagged word to a C pointer/length ABI; a direct
C probe succeeded on the same directory. Source review includes pure lowering
and dynamic-directory regression cases; corrected producer and real manager
worker dispatch remain pending. Shared Linux runtime repair is draft PR2166;
Windows archive symbol-format inspection passed, while a native Windows nm DLL
loading issue remains a tooling compatibility check before deployment.

### 2026-10-02 correction: whole seven-item scope is not coding-complete

The original seven-item authority is
 doc/03_plan/seven_plans_host_completion_2026-09-29.md:
platform unification, SCV/text database, typed collections, linker, optional
provider size/startup, compile optimization, and profile/proof dispatch.
Merged portions of items1/5 must not be described as their entire planned
implementation. The earlier conversation figure2/7 coding-complete was too broad
and is withdrawn. No whole item is currently certified implementation-complete;
this is not a claim that zero code has been written.

Fresh release-head audit still identifies code gaps: general parser/provider
execution and platform support (item1), cache settlement/publication (item2),
collection-selection/identity-map integration (item3), linker completion (item4),
general first-demand provider packaging, release-small/no-unwind proof and dual
provider dispatch (item5), full graph/scan-free warm/concurrent builds (item6),
and remaining profile-chain/selection integration (item7). Native verification
is additionally outstanding. Exact requirements must be recounted at current
release before quoting per-item coding percentages; Oct1 bf28063 requirement
counts are historical and cannot serve as current code-volume percentages.

Current runtime work continues separately: two Windows LLVM collectors remain
active; the unstarted third-job dispatcher was paused to reserve a4GiB manager
rebuild slot. Linux coordinator184 is running only the reviewed serialized SCV
cold/warm admission probe, never automatic full parallel dispatch in this attempt.

### 2026-10-02 user stop and release landing (historical checkpoint)

The user instructed: stop further items1/5 work, push fixes/update docs, then
land on release and stop. All session-owned Windows/Linux builds are stopped.
No automatic resume is authorized by this checkpoint. The bootstrap goal is
paused, not achieved; items1/5 are stopped at partial scope, not marked complete.

Completed reviewed source fixes landed on release/1.0 through PR2163 (manager
directory ABI),2164 (snapshot semantic-text ABI),2165 (interpreter argument
facade),2166 (complete Linux runtime authority). Native manager dispatch and the
snapshot fix remain unverified; merging source does not certify full bootstrap.
Both Phase2 producers passed actual hello compile/run before stopping.

Windows final diagnostic module counts: Phase3LLVM23/13,745 attempted,0PASS;
Phase4LLVM22/13,745 attempted,0PASS. Both collector sessions terminated and
owned process count is zero. Stop receipt:
D:/dev/bootstrap-memory-fix-validation-20261002/phase34-direct-v5/user-stop-result.env
SHA256ea4519edc472d6df545b4428c9851a37ad1c3ec2e60e96335ba020e3a16e456d.
The waiting additional-binary dispatcher stopped before its next claim.

Linux initial parallel route46admission failures is quiescent. The corrected
cold probe reached MIR then SIGSEGV(exit139),peak284700KiB,quiescent1; warm
admission and full inventories did not run. Backtrace is retained at
D:/dev/linux-mir-crash-20261002/gdb.log. Corrected manager seed build was stopped
with exit130 and its cgroup emptied/removed; no rebuilt manager was validated.

Caches and logs are preserved. PR2167 remains draft: regression/report only,
not a production parser-memory fix. Eight uncommitted parser candidate paths
remain in D:/wk-ordinary-parser-retention-20261002; unfinished discard assignment
work remains in D:/wk-hir-discard-assignment-20261002. Do not include those dirty
changes in a future release without review and verification. Public main was
not rebased or force-updated; earlier ruleset-change question was not approved.

### 2026-10-02 resumed bootstrap checkpoint

The user resumed the original goal, fixes, release integration and stale-temp
cleanup. The goal tracker is active. The earlier stop is historical; items 1/5
remain stopped at partial umbrella scope, not marked complete.

The integration owner verified release `d6b569ace4c3ab7b463eab81ac9b2921f032d936`
after PR2170,2177,2178 merged externally following conflict resolution. Earlier
PR2169,2171–2176,2179,2180 also landed. Source merges do not establish deployment
or erase known failed/unrun verification. Mail CI/native-helper proof, imported
global executable tests, and parser retention/performance gates remain open.

Windows producer `70da44fb` built 1,118 modules without failures and compiled/ran
hello. Its source is immutable and predates current release. The direct
Phase3/4 coordinator PID39524 was verified live by process command line; latest
owner counts were 135/13,746 and 60/13,746 LLVM module rows, respectively.
Rows are attempts, not successes. Six Phase4 LLVM app-binary attempts failed;
Cranelift is not started. Both backends still require one actual test runner
executing the compiler, interpreter and loader suites. Receipts and caches:
`D:/dev/windows-parser-08e1-validation/phase34-direct-v2`.

Linux producer `7cc8409e` built 1,122 modules without failures. Pattern-presence
native regression passed. Loader now completes 11 MIR modules without the old
crash, but fails with 36 diagnostics in 12 groups and 18 placeholder warnings.
Evidence: `D:/dev/linux-mir-crash-20261002/pattern-loader-7cc/evidence.json`.
Remaining errors have fix owners; full bootstrap is not passing.

Manager worker admission exposed a Rust signature-table text ABI truncation.
Reviewed fix `252d70dc9e` is landed; a new guarded producer build from release
`70e835667a` is running under a 4 GiB cgroup. Native ABI, actual worker/compiler
task, settlement and both-host go-to-end qualification remain required before
switching bootstrap scripts to the manager.

Shared-cache tests landed, but actual bidirectional frontend reuse/private
isolation remains unverified. Windows `_fullpath` is lexical, not proof of
physical directory alias isolation. A SOSIX identity/ancestry fix is assigned.
Do not infer deployment from merges or cache HIT traces alone.

Preserve active worktrees, producer-bound caches, pinned runtimes and evidence.
Apply fixes to new immutable candidates, never running snapshots. Cleanup only
confirmed stale disposable files. Rerun affected failed criteria after fixes,
not unchanged green checks. Placeholder output cannot establish semantic PASS.

### 2026-10-02 uncapped diagnostic and manager checkpoint

This checkpoint supersedes the live-process observations above. Windows v2 is
closed as a partial diagnostic: 143 Phase3 and 82 Phase4 actual module attempts
are preserved. Later blocked rows were not compilations. The reviewed v3 resume
route is prepared but has not launched; its old producer is not current release.

The separate Windows LLVM full-CLI diagnostic had no process or Job memory
limit. It processed 2,493 source files, then reported 130 parse failures and
exited 1. Processed is not parsed successfully. Peak RSS was 8,281,864 KiB;
peak Job commit was 8,558,700 KiB. There was no host-pressure stop or exception,
and the owned process tree is quiescent. Source hashes matched before and after.
No executable was produced. Detailed parser messages are missing despite the
aggregator's reference to earlier output; the frontend owner is investigating.
Evidence: `D:/dev/uncapped-logic-build-20261002/full-cli-llvm/result.json`.
The separate Astra memory lane still targets a real 7 GB qualification; removing
the diagnostic cap is not a memory fix.

Linux's exact `d6b569ace4` Phase2 attempt compiled 1,129 modules without compile
failures but failed linking `unreachable_hir_variant` and `hir_visit_nothing`.
The 2 GiB guard completed quiescently, peak RSS 1,621,452 KiB. There is no new
producer or hello gate. Generator/import repair and a separate wrong-method
dispatch investigation have owners. Evidence and retained object classification:
`D:/dev/bootstrap-failure-catalog-20261002/currentd6/classification.json`.

The corrected Linux seed, compiled capacity ABI probe and matching native-all
archive passed. The diagnostic manager manifest and builder images compiled;
builder SHA-256 is
`da68d514bde637ff5794bc977fe05675488582e7c13e4d51819d4729cc8f561c`.
The worker image is the next guarded stage. Actual worker/compiler execution,
failure isolation, Windows qualification and Phase2-built deployment are still
unproven. Diagnostic seed-built images do not satisfy canonical deployment.

SOSIX directory identity native C tests passed on both hosts and source review
found no remaining P0/P1. The generated Simple ABI attempt failed earlier in
the old producer's library MIR closure, so directory ABI execution and actual
bidirectional frontend cache hydration remain unverified. Evidence:
`D:/dev/shared-cache-root-proof-20261002/linux-native-abi-run1`.

Canonical scope is broader than the four-root diagnostic inventory. On d6,
the latter contains 13,752 files; repository module-role policy yields 17,147
static production candidates after three explicit fixture exclusions. OS
modules are required and `src/unit` contains measurement classes. Actual
snapshot/role receipts must qualify this inventory before claiming completion.
See `D:/dev/bootstrap-crosshost-apply-verify-20261002/linux-d6-draft/CANONICAL-SCOPE.md`.

### 2026-10-02 manager compiler-task milestone

The Linux diagnostic manager now executed a real compiler task successfully:
manifest admission, worker dispatch, native compile/link, output verification,
and executable startup passed. Exactly one attempt produced `Hello World\n`
with empty stderr. Worker reaping and matching capacity acquisition/release
receipts plus settlement were verified. The initial private output comparator
omitted the newline; correcting that read-only comparator required no rebuild.
Evidence: `D:/dev/manager-bootstrap-verification-20261001/release-243db-scanner-images-linux/compiler-hello-release243-v4`.

This proof uses the older 6b9 source/producer and seed-built manager images.
It does not qualify new Phase2-built manager deployment, Windows execution,
grouped failure isolation, or complete module inventory execution. Earlier
attempts exposed missing staged headers; all failed attempts and their caches
remain preserved. The successful task explicitly allows only one attempt.

The next shared bootstrap source is `fa703ca0e1814e2a7ec9b9305378df449373b643`,
tree `e1d9575a6821f9240ef8adf0b18585701eec650b`. Its independently checked
inventory contains 17,147 compile modules and three explicit exclusions.
Both host builds are in progress; no new producer/hello PASS is recorded here.
Separate diagnostic routes may start after actual hello with identity/resource
checks, as requested, without representing themselves as canonical admission.

### 2026-10-02 disk-admission stop and exact resume state

Linux fa703 Phase2 linked successfully: 1,130 compiled, zero reused or failed;
producer SHA-256 `079e0afc5478bc28ba9f02b13d563b8f20d2d85e35ac7c780f231cdbdb67cab9`.
The first hello compiled and ran, but used an unsupported runtime-path variable,
so it is not a provider-qualified handoff. The changed explicit-provider hello
attempt crashed during parsing (exit 139); it also newly enabled `--verbose`.
A third controlled attempt without that flag is prepared, not executed.

The corrected provider contract is explicit `auto`, an immutable directory
containing only native-all archive `adb88fb1739ddcf73396cd5e6255a9e5474ca61d5f5088d675137f6214c1c4b0`,
and `SIMPLE_PROJECT_ROOT` identifying the frozen fa703 C-runtime source.
Manifest `D:/dev/linux-integrated-release-d6-20261002/helper-panic-candidate/runtime-auto-manifest.json`
has SHA-256 `6bff40ffd11361446302b877ba190d087c9af31792703cb2ef41256cf42acc36`.
This supersedes the unsuitable named core-C/two-archive contract. Source review
accepted the corrected selectors; actual provider-bound hello remains unproven.

Windows fa703 native-all, backfill and seed builds all passed. Its launcher
refused Phase2 before spawning a child because D had less than 27 GiB free.
The exact stop receipt is
`D:/dev/windows-phase2-release-next-20261002/resource-stop-phase2.env`.
After fresh disk and memory admission, `run-fa703-phase2.shs` can resume using
the verified runtime snapshot without rebuilding those passing prerequisites.

Twelve sealed old trace logs were losslessly archived (3.09 GiB less stored
data), with decompressed hashes verified; three clean merged source worktrees
were removed with owner confirmation. Commits, tests and external evidence
remain preserved. Actual D free space was still about 25.32 GiB afterward;
do not count logical archive reduction as available disk. Restore manifests
are under `D:/dev/temp-cleanup-20261002-resume`.

The diagnostic Linux manager also passed the two-task keep-going criterion:
a compiler parse failure was followed by an independent successful hello build,
both reaped with capacity settled; overall build status correctly stayed failed.
See `D:/dev/manager-bootstrap-verification-20261001/manager-qualification-result-20261002.md`.
No Phase2-built manager deployment, Windows manager qualification, shared-cache
hydration proof, or completed Phase3/4 inventory is claimed. Preserve prepared
17,147-module routes and all producer-bound caches during the resource stop.

### 2026-10-02 stage disk admission and terminal Linux hello

This checkpoint supersedes the resource hold above for Windows Phase2 and the
third Linux hello only. Auditing the remaining stages justified a private
11.5 GiB disk admission threshold, 8.5 GiB emergency floor, and observed
volume-depletion budgets of 2 GiB for Windows Phase2 and 1 GiB for Linux hello.
Physical-memory, commit-headroom and RSS checks remain enforced. The new guards
fail closed on missing probes and sample disk again after owned-process cleanup.
These are sampled safeguards, not filesystem quotas or full-inventory budgets.
Historical guards and receipts remain unchanged. Evidence:
`D:/dev/capacity-admission-verification-20261002/stage-disk-guard-verification.md`.

Linux's third provider-bound hello failed with compile exit 139 during parsing,
before runtime compilation or linking; executable startup was not attempted.
Removing `--verbose` did not resolve the crash. Provider hashes stayed unchanged,
peak RSS was 168,672 KiB, observed disk depletion was zero, and owned processes
were confirmed quiescent. The three-attempt limit is exhausted: no fourth probe
is authorized by this checkpoint. Phase2 producer creation remains PASS, but
provider-qualified hello, Phase2-built manager images, and Phase3/4 are blocked.
Evidence: `D:/dev/linux-integrated-release-d6-20261002/helper-panic-candidate/hello3-terminal/gate.json`.

Windows Phase2 actually started at 09:53:35 UTC under the revised guard, using
the unchanged fa703 source and passing runtime snapshot. Root process 43320 and
compiler process 43156 were subsequently observed live. Current source roots,
materialized junction targets and pinned receipts were checked before launch;
passing runtime prerequisites were reused. No Windows Phase2 completion or hello
PASS is claimed at this checkpoint. Launch identity and admission evidence:
`D:/dev/windows-phase2-release-next-20261002/launch-v2.json`.

The full objective remains open: Phase2-built manager deployment on both hosts,
actual shared-cache hydration, and complete Phase3/4 module and executable/test
builds require separate evidence. Preserve all producer-bound caches and the
17,147-module routes; the narrow disk policy above does not admit those queues.

### 2026-10-02 Windows Phase2 candidate linked

Windows fa703 Phase2 completed at 10:07 UTC: 1,130 compiled, zero cached and
zero failed, with 797.0 seconds compilation plus 38.7 seconds linking. Candidate
`D:/dev/windows-phase2-release-next-20261002/phase2/stage2-fa703.exe` has SHA-256
`c82956eb610fadd603533fb4eb61e30236b895ff665b1bf05997edfdbe3ecac1`.
Owned-process supervision reports exit zero, quiescence and peak RSS
1,915,728 KiB. This was sampled RSS enforcement with Job Object containment;
the receipt explicitly records `hard_memory_limit=0`. Disk admission and final
samples were 26,905,067,520 and 26,395,930,624 bytes respectively, without a disk
stop. Provider-bound hello and canonical Stage2 admission remain unproven.

The next diagnostic manager qualification requires three Phase2-built images
under one cumulative 2 GiB disk-growth guard after actual hello. It does not
replace the canonical eight-image preparation or its typed admission receipt.
The existing grouped-native manager already restores its complete manifest
ledger; retain that ledger and the full 17,147-module inventory when planning
bounded resource admission. No partial inventory is a completion substitute.

Review of the downstream direct runner found both repeated per-module source
scans and an old four-root source-check scope. The proposed correction performs
checks at inventory boundaries and covers all source and relevant test paths.
Focused rejection tests and independent review must finish before that runner
is used; no full Phase3/4 queue is claimed started here.

### 2026-10-02 Windows hello resource stop and retained inventory

The first actual Windows hello workload ended with `disk-budget-stop`, not a
compiler result: whole-volume depletion was 1,172,066,304 bytes against the
1 GiB allowance. Owned processes were reaped; peak RSS was 1,890,596 KiB.
No executable or passing hello binding exists. The hello-local cache was
empty, but owned SCV state under the frozen source's `build/scv` retained about
227.5 MiB; the rest of the observed volume loss remains unassigned.

SCV published generation 1 with a valid inline v3 event cursor in
`source-inventory/CURRENT`; the absence of the legacy separate cursor file
does not invalidate it. Generation and membership hashes were checked, but
the snapshot is incomplete. The next attempt will retain these caches and use
the supported warm-inventory acquire path (`SIMPLE_SCV_INVENTORY_COLD_INIT=0`),
allowing the compiler to validate and construct its own snapshot. Never promote
the temporary snapshot or invent authority receipts.

A separately reviewed second-attempt policy is being prepared with a 2 GiB
aggregate allowance, 10.5 GiB disk admission threshold and unchanged 8.5 GiB
emergency floor. Old receipts remain immutable; actual warm admission and hello
execution are still unverified. The three manager-image scripts are reviewed
but unlaunched, pending a genuine hello PASS. Evidence:
`D:/dev/windows-phase2-release-next-20261002/hello/cold-admission-observation.md`.

### 2026-10-02 Windows hello PASS and manager image batch started

The second Windows hello attempt passed compile and execution with exact
`hello\n` output. The Phase2 producer remains `c82956eb610fadd603533fb4eb61e30236b895ff665b1bf05997edfdbe3ecac1`;
the executable SHA-256 is `484939a1496802ebd20c68f330cd699440280ae502e710006f2dfd75bf7f051f`.
Warm inventory validation reached snapshot construction and actual worker
execution. Source/runtime identities were rechecked afterward. The guard
reported completed/zero exit, quiescence, and peak RSS 5,369,848 KiB under the
unchanged sampled limit. This is a diagnostic hello PASS, not canonical Stage2
admission. Evidence: `D:/dev/windows-phase2-release-next-20261002/hello/attempt2/binding.env`.

The copied 23 GiB host threshold included historical Linux, manager and parser
reservations. Those jobs had ended; the reviewed admission formula now requires
7,000,000,000 bytes plus an 8 GiB host reserve plus explicit other reservations,
against both available physical memory and commit headroom. Runtime RSS
enforcement was not reduced. D free space increased externally during hello;
this lane claims no cleanup or reclaimed-space attribution.

One reviewed Phase2-built diagnostic manager batch has now started, sequentially
building manifest, Windows builder and Windows worker within one cumulative
2 GiB disk budget. The canonical eight-image preparation, actual manager task
qualification, full Phase3/4 queues, and cross-host cache proof remain pending.
Linux remains stopped at its three-attempt hello limit. All prior cache and
failure evidence remain retained.

### 2026-10-02 manager image failure and frozen-seed dispatch defect

The first Windows manager-image batch ended with workload exit 1 on its manifest
image. No image was sealed; builder and worker were not started. The guard
confirmed quiescence and peak RSS 4,716,072 KiB, without a resource stop.
The retained worker output reports 32 distinct library parse-failure paths in
a 50-file closure. Cache counters show 18 hits and 32 misses, but no per-file
hit association proves that those sets are identical. Neither the outer log
nor the retained full worker-stdout spill contains actual parser token/line
payloads. The spill's generic filename says stderr; its capture provenance is
worker stdout. Preserve both streams and do not infer syntax edits from summaries.

Source review found PR2208 targets a different streaming path. PR2213 would
restore diagnostics on this ordinary path, but is not a proven parse repair;
its existing native retry limit remains in force.

A separate bounded codegen review proved the frozen seed lacks landed fix
`9e190c6642` (PR2205). Retained COFF code calls `SqlBlockDef.kind` on a newly
constructed `MathBlockDef`. This is a real dispatch defect, but its relationship
to the manager parser failures is unproven. An isolated bootstrap source with
only that already-landed seed fix is being prepared; the old fa703 source and
caches remain unchanged. Evidence: `D:/dev/fa703-seed-dispatch-readonly-review-20261002.md`.

Direct Phase3/4 fallback identities retain all 17,147 modules, but no queue has
launched. The new paired monitor still requires fixes for cleanup proof and
bounded timeout handling before resource admission. Canonical manager deployment,
full module completion and cross-host cache qualification remain incomplete.

### 2026-10-02 full-queue guard review and resource admission

The paired monitor's cleanup-proof and bounded-wait fixes passed focused
negative tests and independent source/evidence review. Missing or malformed
Job receipts retain ownership markers and produce containment-unverified;
disk-stop handling drains owned lanes with finite deadlines. The review is
`D:/dev/capacity-admission-verification-20261002/phase34-paired-disk-monitor-review.md`.

The next fresh admission refused the pair before any native launch: available
physical memory was 22,125,076,480 bytes, below the 22,589,934,592-byte requirement
for two 7 GB jobs plus an 8 GiB host reserve. Commit headroom and disk passed.
A serial full-scope route is being prepared; no thresholds were reduced and
all 17,147 modules, both backends and requested suites remain in scope.

The isolated seed-dispatch candidate is now `edea133ff0bbdd9d48a300a3d008723aece8399d`,
exactly fa703 plus landed fix `9e190c6642`, with matching patch identity. Source
materialization, canonical Cargo-cache compatibility and a private guard are
being prepared before its canonical Stage2 bootstrap. No new seed build has
started. Linux's three-attempt stop and the manager batch failure remain in force.

### 2026-10-02 Windows full Phase3/4 queues launched in parallel

At 11:36:45 UTC, the reviewed diagnostic coordinator started both Windows
queues with the same hello-qualified Phase2 producer and frozen fa703 source.
The coordinator PID 43068 was independently observed live; its first active
task guards select the Phase3 LLVM bootstrap and Phase4 LLVM bootstrap tasks.
All 17,147 modules remain selected, with LLVM then Cranelift and the requested
binary/test-suite tasks. Launch is not module completion or canonical admission.

The policy enforces sampled RSS limits of 6 GB for Phase3 and 7 GB for Phase4,
both within the requested 7 GB maximum, while retaining the 8 GiB host reserve.
Fresh physical memory was 21,604,638,720 bytes against a 21,589,934,592-byte
requirement; commit headroom was 36,422,746,112 bytes. D had 36,898,639,872 bytes
free. Disk accounting retains the conservative cumulative shared-volume limits.
Boundary tests, a harmless real Windows Job, and independent review passed
before launch. Evidence: `D:/dev/windows-phase2-release-next-20261002/phase34-full/paired-disk-admission.env`.

The corrected edea seed source has separately passed materialization and source
verification. An independent Cargo-cache copy preserves the old cache; canonical
Cargo freshness checks are still required. Its native bootstrap remains held
while the two diagnostic Windows queues own their resource reservations. Linux
and canonical manager admission remain incomplete; no earlier failure was reset.

### 2026-10-02 first parallel binary results: HIR memory limits

Both first LLVM bootstrap-entry jobs exited 88 after their sampled RSS caps
were exceeded; their Job receipts confirm quiescence. Phase3 peaked at
5,864,184 KiB against 5,859,375 KiB; Phase4 peaked at 6,891,708 KiB against
6,835,937 KiB. Phase3's last bounded progress marker was HIR module 80/1,084.
These results establish memory-limit failures, not successful binaries or
source-parser failures. Preserve the task rows and process-tree receipts under
`D:/dev/windows-phase2-release-next-20261002/phase34-full/receipts/`.

The coordinator continued independent work without retrying either failed
binary: Phase3 advanced to its complete LLVM module inventory, and Phase4 to
its LLVM full-CLI binary. No live source or guard was edited. A source-only
memory investigation is comparing the retained evidence with existing fixes.
The corrected seed's separate nested-supervisor fixture also exposed a helper
cache path-conversion failure; its narrow environment fix remains unverified.

### 2026-10-02 stale producer retired; replacement synced to release

The fa703 queues were retired through their owned stop protocol because that
frozen source omits landed fixes, including PR2200's HIR serialization scratch
scope. The coordinator, lanes, guards and compiler children are gone; positive
Job receipts and the paired terminal confirm quiescence. Both reservations are
released. Old source, caches, outputs and failure receipts remain preserved.

Phase3 completed 28 actual module Jobs: six passed and 22 failed. A cancellation
propagation bug then recorded 77 synthetic exit-143 rows without compiler
children, plus one incomplete attempt directory. These are unattempted work,
not additional compiler failures. Phase4 retained four actual binary results.
Evidence: `D:/dev/windows-phase2-release-next-20261002/phase34-full/retirement-evidence.env`.

The clean replacement worktree was synced to release commit
`7734f947be8ba9465d0ba312170681074e990587`, including the landed ownership, AST,
HIR and diagnostic fixes. Materialization and the corrected nested-supervisor
fixture are proceeding under fresh resource admission. This candidate has not
built yet. Complete source inventories, both backends, canonical manager
admission and Windows/Linux cache qualification remain required and unfinished.

### 2026-10-02 replacement canonical bootstrap entered Rust seed compilation

The frozen release `7734f947be` passed materialization and fresh source-consumer
verification, then entered the guarded canonical bootstrap. At 12:32 UTC its
progress state advanced to Rust seed compilation; an actual `rustc` child was
observed compiling `cranelift_codegen`. The seed build uses locked/offline Cargo
and the independently copied configuration-keyed cache, with normal freshness
validation. This is build progress, not seed or Stage2 admission.

The launch retains a decimal 7 GB sampled Job RSS cap, 8 GiB host reserve,
8 GiB cumulative D-volume growth budget and 8.5 GiB disk floor. Cargo and native
jobs are explicitly one. The actual canonical arguments request both genuine
Stage3 and managed Stage4 planner receipts after Stage2 admission, using
`verify-landed-compiler-fix` and `self-host-convergence-check` respectively.
Evidence and live progress: `D:/dev/windows-release-7734-build-20261002/`.

The Windows nested-supervisor fixture passed with actual new/inherited Jobs;
its corrected test landed in PR2240. Collector cancellation, including the last
partial batch, passed focused regressions and landed in PR2242. Neither result
proves manager deployment or cross-host compiler-cache reuse. Those integration
lanes remain active, with no changes to this frozen compiler source.

### 2026-10-02 managed continuation candidate and outstanding scope

The isolated `D:/dev/managed-go-to-end-20261002` candidate distinguishes a
reaped compiler ERROR/1 from transport, admission, timeout, cancellation and
unknown failures. Its shell scheduling regression passed; compiled Simple
acceptance tests and independent review are still outstanding. This is not a
deployed manager or evidence of complete module traversal.

Root review found that the initial scheduler's 20 outcomes cover 12 binaries,
four indexes and four module groups. Source review confirmed that the requested
interpreter binary and six later compiler/loader/interpreter suites are absent
from this canonical schedule; prerequisite Stage2 tests do not cover them.
Phase3/Phase4 are serial with no outer parallel scheduler. Implementation and
admission design are assigned; do not equate 20 outcomes with complete scope.

Manager preparation compares the full tool source snapshot with the admitted
Stage2 source. Therefore this patched manager cannot be attached to the running
`7734f947be` candidate's receipts. Build it through a subsequent candidate that
contains the fixes; retain the current build and its cache meanwhile.

The proposed shared parse CAS aliases are `D:/dev/simple-shared-parse-cas-v1`
and `/mnt/d/dev/simple-shared-parse-cas-v1`. Configuration alone is not cross-host
reuse proof. Keep native outputs and writable producer/backend caches isolated;
actual Windows/Linux identity and reuse qualification remain outstanding.

The live replacement candidate subsequently completed `rust-seed-build` in
11m26s with supervisor and native process status zero. It advanced to
`rust-rust-native-all-build`, with new Cargo/rustc children observed. This proves
the seed build step, not Stage2 admission or a Phase3/Phase4 executable.

Independent review identified two continuation safety gaps in the manager
candidate: restored FAILED receipts must be re-admitted before any new dispatch,
and unknown transport/poll/collection outcomes must stop new dispatch while
existing children are cleaned up. Both are assigned for correction; the patch
is not approved for deployment yet.

Acceptance-scope review also found that the retired diagnostic's selected
compiler/interpreter suites contain toy assertions without exercising those
subsystems. A nonzero `Results:` count alone cannot qualify them. Its test
environment points `SIMPLE_BINARY` at Phase2 and never invokes the new Phase4
interpreter. Replacement acceptance must bind and execute the actual Phase4
artifacts on meaningful positive and negative fixtures; the existing loader
spec has real loader imports but still needs the correct produced-tool binding.

The same canonical run completed `rust-native-all-build` in 7m16s with
supervisor/native status zero, then entered `rust-rust-runtime-nolto-build`.
Fresh Cargo/rustc children were observed; no restart or Stage2 admission is
implied by this intermediate runtime-build milestone.

### 2026-10-02 replacement candidate entered Stage2 compilation

All four Rust Cargo steps completed with native/shell status zero. The final
compiler backfill took 1m12s; the post-build source fingerprint completed
naturally. Preflight then passed five checks with zero failures and zero skips.
The same guarded run entered `milestone=stage2` with an actual seed-backed
`native-build` child and `logs/x86_64-pc-windows-msvc/stage2-native-build.log`.
Its seed reports that dynload is unsupported and emits a single native
artifact. Stage2 completion, admission and planner receipts are still pending.

The proposed shared-cache qualification requires unlanded physical-directory
owner/runtime exports from `D:/dev/shared-cache-root-identity-20261002`.
Read-only comparison with release `8aa06c7ffc` confirmed they are absent;
configuration files alone cannot enable or qualify that API. Prepare the
reviewed source change for a subsequent candidate rather than patch this live
source or claim generated-Simple cross-host reuse from native C tests.

### 2026-10-02 Stage2 linked, then canonical sanity rejected the candidate

Stage2 native-build completed 1,136 modules, zero cache hits and zero compile
failures (1229.1s compilation plus 83.8s linking). The linked 19,974,144-byte
candidate is preserved as `stage2/x86_64-pc-windows-msvc/simple.exe.rejected`,
SHA256 `2f3d16fdfaaafcdb630361dd37ed62fe8cef171946b245fe88629b6e5d5f0384`.
The canonical sanity gate failed, and the overall run exited 1. The terminal
Job receipt confirms quiescence and peak RSS 4,446,264 KiB, below the sampled
6,835,937 KiB cap; this was not a memory or disk stop.

All advertised sanity evidence/log files are absent. The source has early
session-contract and frontend-capture setup returns before those logs, so the
compiler's runtime failure and actual sanity invocation count are unknown.
Astra is investigating these gates with a bounded helper-only reproducer;
there is no hello-world PASS, Stage2 admission or planner receipt. Manager and
Phase3/Phase4 launches remain held. Preserve the rejected artifact and caches.

### 2026-10-02 sanity wrapper diagnosed; diagnostic hello reached SCV admission

The helper-only reproducer proved that MSYS converted the portable session
helper's POSIX path into `D:/...`; the sanity gate then returned 125 before
creating its frontend logs. PR #2251 preserves this environment path and adds
explicit diagnostics for the early 125/126 failures. Its third and final
focused regression passed with a quiescent Job; do not repeat those fixtures.
Release landing remains pending the new test script's CI registration fix.
This proves the wrapper defect, not a successful compiler sanity invocation.

One actual diagnostic invocation of the preserved `2f3d16f...f0384` compiler
then exited 1 at SCV admission: `compile-event-journal-missing`. No hello
artifact or code generation was reached. Evidence is under
`D:/dev/windows-release-7734-build-20261002/rejected-hello-cycle2/`; the sibling
`.resource.env` and `.resource.env.process-tree.env` receipts show workload
failure, quiescence, and peak RSS 440,172 KiB. The outer status 74 records the
diagnostic wrapper failure; it must not replace the actual compiler status 1.
A prior missing `out` shell variable stopped setup before any compiler call.
Attempt directory names therefore are not compiler invocation counts.

Review first-checkout SCV cold initialization and its disk budget before one
changed retry. Retain all prior evidence and caches; no unchanged retry or
canonical admission marker is authorized by this diagnostic result. Phase3
and Phase4 remain unlaunched on this candidate until actual hello success.
The old Linux lane remains held after three failed hello attempts.

The manager candidate now declares 28 outcomes: 14 binaries, six meaningful
acceptance suites, four indexes and four module groups. Its isolated direct
bootstrap fallback matrix has 24 tasks because it omits manager index tasks.
Classification, parallel admission, strict tool/runtime binding, and suite
evidence changes are implemented or under source review; native/SSpec checks
remain unrun. Capture-only tool configuration must not activate strict
compiler discovery until sealed authority selectors exist. Shared Windows/
Linux parse-cache qualification is still pending; no deployment or complete
module traversal is established by these source and shell checks.
