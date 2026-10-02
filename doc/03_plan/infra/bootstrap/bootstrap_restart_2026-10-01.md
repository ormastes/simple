# Bootstrap restart — 2026-10-01

This supplements the [historical Windows restart](windows_bootstrap_restart_2026-09-22.md).
It records incomplete work, not build admission or permission to publish.

## Latest checkpoint: 2026-10-02 cached builds resumed

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
