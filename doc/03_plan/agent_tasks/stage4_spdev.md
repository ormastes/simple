# Stage 4 SPipe agent tasks

## Current status after final cycle 3 (superseded 2026-08-14)

This section is historical diagnostic context. The current authority is
TODO666 plus
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`;
the cycle-3 Stage 2 below must not be used as current admission evidence.

- Final cycle 3 repaired both source frontiers and published current-source
  Stage 2 at `build/restart12-riscv-current/stage2/x86_64-unknown-linux-gnu/simple`.
  Its binary SHA-256 is
  `e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`;
  the Stage 2 log SHA-256 is
  `db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`.
- Stage 3 was terminated by host `earlyoom` at 09:52:45 with SIGTERM/143 when
  the `simple` process reached 41,394 MiB RSS and the no-swap host had less than
  10% free memory. It exited 5.4 seconds later. The empty Stage 3 log SHA-256 is
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`;
  no Stage 3 executable was produced.
- The 41,394 MiB reading is an interrupted high-water mark, not a proved root
  cause, completion budget, or remedy. That Stage 2 predates the complete
  snapshot provider. TODO666 first owns non-circular independently verified
  Stage2-tuple planner admission, admission-grade phase publication,
  full-bootstrap evidence wiring, hard-bounded zero-survivor process-tree
  supervision, strict analyzer publication, and compatible provenance
  verification. The latest four component drafts were rejected and reverted at
  their individual three-cycle boundaries; a fresh current-HEAD Stage 2 then runs one
  instrumented Stage 3 in a fresh session. A2 remains gated; no Stage 4,
  essential-smoke, deploy, or rollback evidence exists.

- SDK contract preparation is implemented, frontier-reviewed, and statically
  gated. It defines `BootstrapSdkManifest`, `BootstrapSdkModuleInterface`,
  `BootstrapSdkBodyArchive`, and `BootstrapSdkProvenance`, but it is preparation
  only and is not binary-reproducibility or Stage 4 evidence.
- FreeBSD QEMU tooling is implemented, frontier-reviewed, and statically gated.
  The preflight contract, bounded operations, deterministic receipt, scoped
  PASS text, and full-run provenance rules are in place, but no FreeBSD QEMU
  bootstrap has been executed or accepted here.
- SimpleOS AArch64 evidence tooling is implemented, frontier-reviewed, and
  statically gated. Producer/consumer provenance, stale-artifact invalidation,
  symlink rejection, receipt revalidation, atomic publication, serial
  watermarks, RAMFB checksum correlation, and signal exit behavior are covered,
  but no image, QMP, hosted bootstrap, or board PASS is claimed.
- Stage 3 remains unadmitted. It is the hard gate for every x86
  Stage 4 and downstream platform acceptance claim. The SDK, FreeBSD, and
  SimpleOS preparation changes do not waive that gate.
- Linux AArch64 and macOS require their respective external native hosts.
  Cross-compilation or an x86 QEMU result cannot be reported as native-host
  PASS.
- SimpleOS x86_64 follows admitted deployment and is not a substitute for x86
  Stage 4 admission.

### Mandatory gate sequence and canonical commands

Every platform lane, including QEMU, cross-target, and external-native-host
lanes, is blocked until this exact sequence completes on x86_64 Linux:

`Stage 3 admission -> x86 Stage 4 -> candidate sanity/hash -> all four essential smoke markers -> deployment -> source-matched platform/feature acceptance -> rollback`

Preparation, static gates, frontier review, cross compilation, and retained
historical artifacts cannot skip or reorder a gate. Run a platform command only
after the merge owner records completion of gates 1 through 5 against the same
source and candidate lineage.

| Order | Gate / lane | Canonical command or authoritative owner evidence | Required result |
|---|---|---|---|
| 1 | Stage 2/3 admission | After TODO666 publishes the accepted planner receipt at `build/bootstrap/planner-admission/restart12-riscv-current-head/admission.env` and accepts the M0 evidence owners, run `env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=build/bootstrap/planner-admission/restart12-riscv-current-head/admission.env --full-bootstrap --backend=cranelift --mode=dynload --output=build/restart12-riscv-current-head --jobs=1` in a fresh session and absent output. Because `--full-cli`/`--deploy` is absent, this invocation stops after admitted Stage 3. Retain planner, phase, memory, process/RSS evidence, Stage 2/3 logs, authority identities, manifests, and hashes. | Fresh current-HEAD admitted pure-Simple Stage 2 and instrumented Stage 3; historical `e383...` is diagnostic only |
| 2 | x86_64 Linux Stage 4 | Run `env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=build/bootstrap/planner-admission/restart12-riscv-current-head/admission.env --resume-stage4-from-admitted=build/restart12-riscv-current-head --deploy --jobs=1`. Keep the deployment active through source-matched Gate 6 evidence. | Fresh non-stub pure-Simple Stage 4 candidate from Gate 1, internal essential smoke exactly once, and deployment receipt |
| 3 | Candidate sanity and hash | Continue the same lineage. Record exact path/SHA-256, identity/version/hash, no-stub/no-failure scan, unsupported-command behavior, sanity output, and unchanged candidate bytes. | One frozen candidate admitted for smoke |
| 4 | Essential-tools smoke | Continue the same transaction; it invokes the checker internally exactly once. Do not start a standalone duplicate smoke. | `stage4-essential-tools-smoke.log` from the same candidate emits all four required markers |
| 5 | Deployment | Gate 2's exact resume invocation owns Stage 4, the internal smoke, and deployment without rebuilding Stage 2/3. | Install only after Gates 1 through 4 pass against the same lineage; retain deployed hash, pre/post-swap identity, `bin/release/<platform>/simple.pre_deploy`, and post-swap `-c 'print(1+1)'` output. Keep it deployed through source-matched Gate 6 evidence unless an isolated immutable bundle is published. |
| 6 | Linux AArch64 native acceptance | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on native AArch64 Linux | Retain `build/bootstrap/stage3/aarch64-unknown-linux-gnu/simple`, `build/bootstrap/full/aarch64-unknown-linux-gnu/simple`, hashes, logs, sanity, and all essential markers |
| 6 | macOS x86_64/AArch64 native acceptance | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on macOS | Retain matching `stage3/<triple>/simple` and `full/<triple>/simple`, hashes, logs, sanity, and all essential markers |
| 6 | Windows x86_64 native acceptance | `bash scripts/bootstrap/bootstrap-from-scratch.sh windows-entry --msvc --backend=llvm --mode=dynload --full-bootstrap --no-mcp --jobs=2` in Git Bash/MSYS2 | Retain `build/bootstrap/stage3/x86_64-pc-windows-msvc/simple.exe`, hash, logs, and scoped wrapper evidence; do not add unsupported full-CLI/deploy claims |
| 6 | FreeBSD x86_64 QEMU acceptance | `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full --download` | Scoped FreeBSD x86_64 QEMU bootstrap PASS with preflight/full receipts, VM and guest logs, guest Stage 3 hash, source/base-image identities, and smoke markers |
| 6 | SimpleOS x86_64 target acceptance | `sh scripts/bootstrap/bootstrap-from-scratch.sh --target=simpleos-x86_64 --output=build/bootstrap --jobs=2` | Retain staged artifacts, manifest, hashes, and logs; target evidence only, not a hosted full CLI |
| 6a | SimpleOS AArch64 attested image | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` | Retain image, producer manifest, compiler/source/kernel/disk/build-log hashes, and logs; image evidence only |
| 6b | SimpleOS AArch64 QMP input | `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` after 6a | Retain atomic evidence manifest, QMP/serial logs, watermarks, captures, and guest/capture checksum equality; QEMU input evidence only |
| 6 | RISC-V64 scoped cross/QEMU acceptance | `sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | Retain matrix evidence; scoped cross execution/SIMD evidence only, not hosted bootstrap PASS |
| 6 | RISC-V32 bare-metal object acceptance | No exact command is published in the session plan. Platform sidecar owns the repository architecture-gate receipt for `riscv32-unknown-none-elf`, including ELF32/RISC-V attributes, toolchain identity, command transcript, hashes, and logs. | Bare-metal object acceptance only; never claim `riscv32-unknown-linux-gnu` or hosted bootstrap PASS |
| 7 | Explicit rollback execution | After all selected source-matched Gate 6 evidence, run `sh scripts/bootstrap/bootstrap-from-scratch.sh rollback-deploy <canonical-triple>`. Earlier rollback is allowed only when TODO667 has published an isolated immutable bundle from which every selected Gate 6 row runs. | Distinct executable rollback receipt is mandatory and cannot predate evidence from the only deployed source-matched authority. TODO667 retains the immutable deploy+rollback bundle-publisher gap; do not create a duplicate Todo. |

### Canonical readiness checker and handoff helper

The canonical readiness checker is:

```bash
sh scripts/check/check-bootstrap-platform-handoff-readiness.shs
```

It is fail-closed and evaluates the retained receipts for the exact source and
candidate lineage. It must not rebuild, substitute the Rust seed, accept a stale
artifact, infer a marker from a log fragment, or turn an unavailable host into a
PASS. A result is `PASS` only when Gates 1 through 5, the selected Gate 6
native/platform handoff, and Gate 7 executable rollback are evidenced in that
order (or Gate 6 is bound to TODO667's isolated immutable bundle). Otherwise
the result is `OPEN` or `BLOCKED`, with the first missing
gate named.

Plans and generated operator manuals use the helper step name
`step_bootstrap_platform_handoff_readiness`. The helper invokes the canonical
checker after Gate 7 rollback, binds the handoff to `<canonical-triple>`, and publishes
the Gate 6 handoff receipt. It is a readiness check, not permission to skip a
gate or to claim platform success.

### Stage 3 ownership and independent work

Stage 3 may be owned and executed by another agent. Stage 4, receipt preparation,
checker integration, and external-host coordination may proceed independently,
but the Stage 4 owner must consume the Stage 3 owner's exact path, SHA-256,
authority identity, and admission receipt. Independent work is preparation only
until that receipt is attached; it cannot reorder Gates 1 through 6 or publish a
Stage 3, Stage 4, deployment, rollback, or platform PASS.

### Required evidence and provenance

- x86 Stage 4: source revision and source-tree identity, exact command
  transcript, admitted Stage 2 authority and runtime authority, Stage 3 path
  and SHA-256, Stage 4 candidate path and SHA-256, pure-Simple compiler
  identity/version/hash, native-build log, progress events, elapsed time and
  peak RSS log, no-stub/no-failure scan, exact-binary sanity output, and
  retained cache identity.
- Essential tools: one fresh candidate must produce exactly these markers in
  the retained smoke log: `essential_test_runner_smoke=true`,
  `essential_lint_smoke=true`,
  `essential_duplicate_checker_smoke=true`, and
  `bootstrap_essential_tools_smoke=true`.
- Deployment: candidate path/hash, deployment command, pre-swap identity,
  post-swap identity, rollback command/path, rollback result, and post-swap
  arithmetic smoke output. Deployment is forbidden before candidate sanity and
  all four essential-tool markers pass.
- FreeBSD: preflight receipt, FreeBSD version/architecture, base-image
  identity/hash, source identity, exact command, VM and guest logs, guest Stage 3
  artifact hash, bootstrap logs, smoke markers, and an atomic full-run
  provenance receipt. Missing or empty guest logs fail the claim.
- SimpleOS AArch64: producer manifest containing schema, source/entry identity,
  compiler receipt/version/hash, producer script/hash, host identity, kernel and
  disk hashes, build-log hash, command, and retained logs; consumer evidence
  must additionally contain QMP/serial logs, pre-injection watermarks, captures,
  guest/capture checksum equality, and atomic evidence publication.
- Native external hosts: host identity, toolchain versions, source and compiler
  hashes, exact command, stage/full artifact hashes, logs, sanity output, and
  essential-tool markers. Host unavailable means open, never PASS.

### Sidecar lanes and ownership

- SDK sidecar: capsule contracts, SDK-001 through SDK-010 assertions, eleven
  synchronized `CAPSULE-*` labels, manual, and test plan. Status: complete and
  frontier-reviewed.
- FreeBSD sidecar: preflight, bounded host/VM operations, deterministic receipt,
  guest-log failure handling, and the preflight spec. Status: implemented and
  frontier-reviewed; execution evidence pending.
- SimpleOS AArch64 sidecar: attested producer, QMP consumer, provenance and
  regression spec. Status: implemented and frontier-reviewed; execution
  evidence pending.
- x86 Stage 4 sidecar: after Stage 3 admission, own the first fatal pure-Simple
  compiler boundary and one adjacent reproducer; preserve the incremental
  cache and stop after three distinct fix/verify cycles.
- External-host sidecar: obtain native Linux AArch64 and macOS evidence and
  attach the required receipts; no local cross-build substitution.
- Merge owner: primary Codex agent in the main integration workspace; only the
  merge owner may combine these lanes or publish a claim.
- Final frontier reviewer: normal/highest-capability Codex, reviewing the
  frozen owned-file diff and every evidence receipt after the exact candidate
  passes its gates and before commit/push.

### Explicit not-claimed boundaries

- No Stage 3 admission or Stage 4 PASS is claimed.
- No x86 candidate, exact-binary sanity PASS, essential-tools smoke PASS,
  deployment, or rollback evidence exists in this status.
- No FreeBSD, Linux AArch64, macOS, SimpleOS x86_64, SimpleOS AArch64, QMP, or
  physical-board platform PASS is claimed.
- SDK preparation does not claim source reproducibility, binary
  reproducibility, Stage 4 admission, deployment, or platform acceptance.
- QEMU image or QMP evidence does not claim hosted native bootstrap or physical
  hardware completion.
- Rust-seed builds, stale artifacts, cross-builds, static source checks, and
  frontier review are not production bootstrap evidence.

## Historical baseline (stale after `f47e3916`; 2026-08-03)

- Exact source revision: `4505aec902a7d58012476bee57202006731ea129`.
- Canonical command: full bootstrap, one-binary, full CLI,
  incremental-unlimited, 32 jobs, 15-second progress, no deploy.
- Stage 3 is admitted and sane at SHA-256
  `daa98e2b841a28ada30663ed817b9b3ec39d7dfcc3b919a47cbc72813c84cbbd`.
- Stage 4 loaded 2,116/2,116 sources and completed all 1,431 module surfaces.
  It then stopped at HIR 43/1,431 in `compiler.tools.lint.main`: duplicated
  payload dependencies `LintLevel` and `LintCategory` conflict between the
  compiler lint model and easy-fix model. The former module-427 enum payload
  boundary was not reached.
- Output: `/tmp/simple-stage4-bootstrap-4505-20260803/output`.
- Progress: `/tmp/simple-stage4-bootstrap-4505-20260803/progress.log` and
  `output/bootstrap-build-progress.events`.

## Remaining work, in order

| ID | Lane | Required result | Current status / owner |
|---|---|---|---|
| `ST4-R1` | HIR closure | Resolve the grouped lint/easy-fix terminal collision, then complete 1,431/1,431 HIR modules and record whether former module 427 clears | Blocked at 43/1,431; claimed in `stage4_lint_enum_terminal_collision_2026_08_03.md`; root merge owner |
| `ST4-R2` | Compiler pipeline | Complete mono, MIR, optimization, LLVM/object generation, link, and produce a non-stub full CLI | Pending R1; same live command, no restart while healthy |
| `ST4-R3` | Candidate admission | Record exact path/hash, pure-Simple identity, provenance, source revision, unsupported-command behavior, and no stub/failure markers | Pending R2; merge owner |
| `ST4-R4` | Exact-binary smoke | Run candidate sanity once, then require `essential_test_runner_smoke=true`, `essential_lint_smoke=true`, `essential_duplicate_checker_smoke=true`, and `bootstrap_essential_tools_smoke=true` | Pending R3; merge owner + independent reviewer |
| `ST4-R5` | Deployment | Atomically deploy only the exact R4 candidate; retain/verify rollback, run post-swap arithmetic smoke, and record deployed hash | Pending R4; merge owner; no seed/stale wrapper substitution |
| `ST4-R6` | Tracking and sync | Resolve the enum/trait bug record only after full-graph proof, update lane evidence, commit only owned files, fetch/rebase with file-count guard, and push | Focused fixes pushed through `4505aec902a`; final evidence pending |
| `ST4-R7` | Current-host follow-ons | After x86 admission, run FreeBSD QEMU, SimpleOS AArch64, and scoped AArch64/RISC-V cross gates named in the session plan | Pending R5; platform sidecars, merge owner reviews; Stage-4 plan/source proof assertions added in `test/01_unit/os/native_build_compiler_provenance_spec.spl` |
| `ST4-R8` | External-host handoff | Keep native AArch64 Linux, macOS, Windows, and hosted RISC-V rows open with prerequisites, exact commands, artifacts, owner, and reviewer | Hosts unavailable here; postponement is not PASS |
| `ST4-R9` | Backend/layer evidence | Repair remaining false-green OpenCL/Vulkan identity, digest recomputation, real multi-module build, and real failed-frontier coverage; regenerate manual and verify with fresh pure CLI | Candidate `a5fff9c14ea` is blocked/unmerged after three cycles; next scoped session |
| `ST4-R10` | Future bootstrap SDK | Implement the post-Stage-4 frozen SDK/two-generation plan without narrowing current full-source proof | Planned in `doc/03_plan/design/bootstrap_sdk_capsule.md` |

Latest failed-run receipt: exit 1 after 37m57s, peak RSS 2,634,216 KiB;
last green HIR module `compiler.tools.formatter.main`; no Stage 4 candidate,
sanity, essential-tools smoke, or deployment exists.

## Failure handling for the live run

1. Stop at the first trustworthy fatal compiler boundary; retain the full log,
   progress frontier, source revision, Stage 3 hash, command, elapsed time, and
   peak RSS.
2. Claim or update the canonical bug record before source edits.
3. Reproduce the exact pure-Simple owner failure with the smallest compiled
   gate and at least one adjacent root-cause case.
4. Assign non-overlapping categorized fixes to sidecars; merge owner reviews
   all findings and rejects source workarounds, stubs, seed fallbacks, and
   cascade diagnostics.
5. Push each verified root fix, refresh Stage 3 once, and use the preserved
   Stage 4 cache for the next distinct cycle. Maximum three cycles.
6. If a collect-all inventory is useful, run it as an isolated diagnostic
   sweep with admitted child/compiler identities. It never substitutes for
   the fail-fast authoritative build.

## Coordination

- Merge owner: primary Codex agent in the main integration workspace.
- Final reviewer: normal/highest-capability Codex after the exact fresh Stage 4
  binary passes the required smoke gates.
- Agents claim bugs before edits and announce owned files before overlapping
  compiler work.
- A Stage 4 session permits at most three distinct fix/verify cycles; identical
  failed commands are not rerun.
- Shared future SDK interfaces are `BootstrapSdkManifest`,
  `BootstrapSdkModuleInterface`, `BootstrapSdkBodyArchive`, and
  `BootstrapSdkProvenance`. Their implementation is post-Stage-4 only.

## Completion evidence

- Fresh Stage 4 native-build PASS log and progress/RSS log.
- Exact artifact path and SHA-256.
- Exact-binary sanity PASS.
- `check-bootstrap-essential-tools-smoke.shs` markers for test-runner, lint,
  duplicate-check, and aggregate PASS.
- Deployment record and rollback path.
- Updated session plan with no obsolete blocker or missing artifact link.
- Current-host platform evidence plus explicit external-host handoffs; an
  unavailable native row remains open and is never counted as PASS.
