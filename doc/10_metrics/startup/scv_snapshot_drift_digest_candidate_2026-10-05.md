# SCV snapshot drift digest candidate

Status: **UNVERIFIED CANDIDATE — DO NOT APPLY**. Native correctness, elapsed-time,
and RSS measurements have not run. TODO 347 remains open. The user requires
snapshot time no greater than equivalent Git commit work and application only
after stability is demonstrated; this document does not establish that gate.

## Last research and selected scope

Reviewed the latest `doc/01_research/local/windows_source_snapshot_latency.md`,
its domain companion, and `doc/08_tracking/todo/windows_source_snapshot_performance_2026-10-05.md`
at base `03278930efc1844d6a63d5ce847135187c79072b`. They already document:

- An unchanged CURRENT shortcut and exact published-snapshot reuse.
- A 16,357-entry Hello snapshot and roughly 295-second invocation-to-publication
  interval, not an exclusively attributed snapshot measurement.
- Multiple per-file integrity reads/hashes and repeated authority validation.
- Broad dependency-selected storage redesigns that have not been selected.

This candidate is a small, semantics-preserving reduction of redundant drift
hashing. It does not change selectors, inventories, generation binding, cache
provenance, publication, chunk verification, source rereads, or file formats.
The separate first-line inventory candidate `9d9db323442` is not included and
has no implied native acceptance from this work.

## Change and correctness boundary

After source bytes have been read and matched against the admitted content
digest, materialization performs its existing final source reread. If its byte
length matches the original and it starts with the entire original buffer, the
bytes are identical; reuse the already admitted digest. For different buffers,
retain the original digest comparison, including its collision semantics.

The 2026-10-02 rejected shortcut used ordinary text equality, which can stop at
embedded NUL. This candidate uses the existing `starts_with` boundary:

- `src/runtime/runtime_native.c:4687` uses explicit lengths and `memcmp`.
- `src/runtime/simple_core/core_string.spl:1374` does the same.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2397` lowers
  this text method to `rt_string_starts_with`, tagging both operands.

These are source-review observations, not proof about a produced executable.
The native fixture explicitly rejects missed equal-length changes after NUL.
The helper assumes the caller has already admitted the original buffer's digest;
it is not a replacement for hashing arbitrary original/digest pairs.

## Executable evidence prepared

- `test/01_unit/lib/scv/compile_snapshot_drift_digest_spec.spl`: empty, ASCII,
  Unicode, CRLF, NUL, length changes, same-size changes, and digest fallback.
- `test/fixtures/scv_snapshot_git_profile/main.spl`: eighteen native comparison
  vectors and actual inventory refresh, snapshot acquire, and authority binding,
  with separate phase timings, generation, revision, and retained allocations.
- `scripts/check/check-scv-snapshot-git-profile.ps1`: paired baseline/candidate/
  Git work, five or more rounds, alternating order, cold/warm/timestamp-only/
  one-file-change cases, p50/p95, process-tree RSS, and exact unique membership
  plus byte verification. Git warm no-change exit 1 requires unchanged HEAD and
  a staged tree equal to the unchanged HEAD tree before and after the command;
  no artificial empty commit is timed. SCV's Git
  index and inventory cursor are aligned outside timing before warm samples.
  Old snapshot bytes and untracked creation/deletion are also checked.

The Git comparison times `git add` plus `git commit` while SCV times the entire
native invocation, including its Git discovery, inventory, and immutable view.
SCV additionally produces a materialized immutable tree. That extra contract is
reported rather than removed to win the comparison. Cold starts use fresh
application caches but do not claim a flushed operating-system filesystem cache.
The default 512-file synthetic fixture is diagnostic; a repository-scale cohort
and realistic source-byte distribution are still required for admission.

Baseline fixture preparation must add the same named comparison helper with the
old unconditional digest implementation to base source, without changing its
materializer. Candidate and baseline must otherwise use identical source,
producer/backend/runtime/options, fixture bytes, and build policy. Preserve
immutable binary and source identities for both. Do not build the baseline
fixture against candidate product source and call it a before measurement.

The harness requires the live canonical owner/collector ancestry, immutable
owner request, and matching twenty-job coordinator reservation, shared total
eighty. A reservation JSON alone does not authorize execution. Every command
runs through the pinned canonical process-tree RSS watchdog in monitor mode
with timeout zero. Standard output and error stream to separate files; refusal
occurs only after output is flushed. Sampler receipts must prove quiescence,
actual exit parity, positive observations, and the pinned helper/source identity.
The cached sampler helper must be prepared and pinned before benchmarking.

An immutable `scv-snapshot-profile-inputs-v1` JSON passed with its SHA-256 names
`backend`, `target`, `producer`, `runtime_manifest`, `helper_cache`, `baseline`,
`candidate`, and `tools`. Every file pin has absolute `path` and lowercase
`sha256`. Each variant has `binary`, `source_manifest`, and `build_receipt` pins.
Source/runtime manifests use `scv-profile-file-manifest-v1` with a unique `files`
array of pins. A `scv-snapshot-native-build-v1` receipt binds exit zero,
binary/source-manifest/producer/runtime-manifest hashes, backend, and target.
Tool pins cover `git`, `bash`, `powershell`, `workload`, `wrapper`, `watchdog`, `sampler_source`,
`sampler_binary`, and `benchmark`; wrapper dependency paths must agree.
The canonical owner's command must directly name the harness, input manifest,
and its hash. `-OwnerLaunch` binds the live reservation/collector/request record.
Identity pins are checked before and after each command; complete source and
runtime manifests are rehashed before and after the cohort.

Each timed case has exactly one sampler invocation and the same pinned PowerShell
command host. Its Git mode runs add and commit together; its SCV mode runs one
admission. Native exit markers must agree with the host and sampler exit status.
Preparation and Git identity oracles run outside that timed workload. There is
no summing of separately instrumented Git add/commit launch costs.

The summary remains diagnostic-only. It retains external sampled tree peak RSS,
but steady RSS is still unavailable, and elapsed time includes the matched sampler
transport and command host. Qualification must assess that overhead and the completed outer-owner
receipt, which cannot exist until this worker exits. No active bootstrap source,
cache, or process may be changed.

Harness-only checks in `scripts/check/check-scv-snapshot-git-profile-oracles.ps1`
passed seventeen assertions against real temporary files and oracle inputs:
duplicate/missing/unexpected/case-altered manifest paths, changed frozen bytes,
wrong no-change exits/HEAD/trees, duplicate receipt fields, and changed file pins.
These checks launch no compiler or benchmark and establish no native performance.
Retained fixture evidence:
`C:/Users/user/AppData/Local/Temp/scv-profile-oracles-ab986575b43a42afb0f9998d507e5d8c`.
The seventeen checks ran during repair before the final common-command-host
addition; the final three PowerShell scripts also passed syntax parsing. The
later absolute-path pin guard and common command host have source review/syntax
evidence only, not an additional execution claim.

## Outstanding gates

Native vector tests, snapshot/spec regressions, optimizer analysis, and paired
performance have not run because all shared execution slots were occupied.
Use the currently admitted P2 selected and pinned by the owner when a slot and
completed harness review are available. The older P2 had known shared-IO/fsPath
failures; do not repeat those unchanged or switch to a Rust seed.
Also retain existing corruption, concurrent publication, alias containment,
generation/provenance, and interrupted-publication checks before stable adoption.
No timing improvement, memory improvement, Git parity, or stable status is claimed.
