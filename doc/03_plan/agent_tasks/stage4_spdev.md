# Stage 4 SPipe agent tasks

## Live authoritative state (2026-08-03)

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
