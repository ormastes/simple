## Closed 2026-09-17 — macOS half implemented and verified on a fresh source-matched seed

Closure marker for the macOS half of this receipt. The detailed
implementation summary, transcripts, and remaining Linux-only rows are in
"## 2026-09-17 update (macOS sweep)" below; this header exists so the closure
is visible at the top. Fresh binary that carries the fix:

`/Users/ormastes/simple/build/cargo-r2/release/simple`
(built 2026-09-17 via `sh scripts/setup/build-gpu-seed.shs` — features
`vulkan,metal,simple-compiler/vulkan-graphics`, all 5 capability probes PASS).

Acceptance state with that binary:
`simple test test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl`
→ 11 examples, 8 passed, 3 failed (stable across two runs). Every row that
can execute on macOS passes, including the row that was the original subject
of this todo ("measures a real owned child tree through the production
facade" — `expect_not(usage.evidence_quality == Unavailable)` now holds with
`SampledTree` quality). The 3 failing rows are the Linux delegated-service
provider rows (`run_in_systemd_resource_scope`) and fail closed honestly on
macOS because `/usr/bin/systemd-run` does not exist; they are not macOS rows
and are out of scope for this receipt. The deployed `bin/simple` symlink was
NOT repointed — it still runs the 2026-09-14 bootstrap seed; redeploying the
fresh binary over `bin/simple` is a separate owner decision.

---

## 2026-09-17 update (macOS sweep)

Owner: runtime/process provider maintainer. State: **macOS half CLOSED**
(see header above); the todo's original "blocked pending a prepared macOS
qualification host" no longer applies — the sweep ran on the M4 host
(Darwin 25.5.0, macOS 26.2 SDK, Apple clang 1700.6.4.2).

### Root causes found (in order of discovery)

1. **`__unix__` guard excluded the entire Unix implementation on macOS.**
   Apple clang does not predefine `__unix__` (only `__APPLE__`/`__MACH__`),
   so `#if !defined(_WIN32) && defined(__unix__)` at the top of
   `src/runtime/runtime_process_owned.c` compiled out the WHOLE Unix section
   for every macOS seed — the binary linked only the common-section ENOTSUP
   fallback stubs. This — not just the pidfd gates — is why every observed
   spawn on macOS returned `runtime_error = 45 (ENOTSUP)` and the facade
   degraded to `ResourceEvidenceQuality.Unavailable`. Fixed by admitting
   `__APPLE__ || __MACH__` (comment documents the predefine gap). All
   previously invisible macOS compile fallout was then fixed: `sigtimedwait`
   (Darwin lacks it; the one call site is unreachable on macOS since
   start_v2/v3 fail closed first — replaced with a sigpending-guarded
   sigwait), missing `(void)` casts, and an Apple-only
   `#pragma GCC diagnostic ignored "-Wunused-function"` for helpers whose
   callers stay Linux-gated (documented in-file; Linux untouched).
2. **Zombie semantics differ on Darwin** (probed 2026-09-17): `getpgid(2)`
   refuses a zombie (ESRCH) and `kill(-pg, SIGKILL)` answers **EPERM** when
   the group has no live member — but succeeds when live descendants remain
   (verified: leader-zombie + live grandchild → kill succeeds, grandchild
   dies). `sysctl(KERN_PROC_PID)` still reads `p_starttime` for zombies
   (verified). Consequences baked into the code:
   - `owned_signal_group_pinned` on macOS validates via start-identity only
     (no getpgid) and treats EPERM from `kill(-pg)` as "group already
     empty", same as ESRCH (safe: owned groups are always same-user).
   - `owned_signal_group` keeps its live-leader getpgid check; EPERM added
     to the success set only on non-Linux.
3. **RLIMIT_NPROC (`ulimit -u`) counts the user's ENTIRE system-wide process
   table on Darwin**, so the Tiny scope's `ulimit -u 32` made every fork in
   the bounded child fail with EAGAIN (`BlockingIOError: [Errno 35]`,
   verified by hand). This is the sibling bug
   `doc/08_tracking/bug/test_runner_ulimit_caps_unusable_on_macos_2026-09-05.md`
   territory. `src/lib/nogc_sync_mut/io/resource_scope.spl` now skips the
   `-u` prefix on Darwin with a loud stderr note, mirroring the file's own
   RLIMIT_AS (`-v`) precedent; `_limit_shell`'s fail-closed path and the
   `-t`/`-n` caps are unchanged. Linux command lines are byte-identical.
4. **KERN_PROC_ALL sizing race**: the macOS tree sampler's two-call sysctl
   pattern fails ENOMEM whenever the process list grows between calls; the
   sampler now refreshes the size and retries (4 attempts) instead of
   silently dropping a sample (a dropped sample erases descendant
   pids/charge peaks — this was the last flake in the tree row).
5. **Spec-file defect (pre-existing, blocking ANY run of this spec on any
   binary)**: `@manual_section("Trustworthy resource evidence")` on line 14
   was a REAL decorator immediately before top-level `describe`; the parser
   requires `fn` after a decorator ("expected Fn, found describe"). Every
   other spec in the repo uses the comment form. Normalized to
   `# @manual_section: Trustworthy resource evidence` (comment-only change;
   the sspec annotation is still machine-visible to source scanners).

### Implementation (all in `src/runtime/runtime_process_owned.c`, existing
### files only; `runtime_process.c` and `process_ops.spl` untouched)

- `owned_start_identity`: `__APPLE__` branch reads
  `kinfo_proc.kp_proc.p_starttime` via `sysctl(KERN_PROC_PID)` and returns
  `tv_sec*1e6 + tv_usec`. Quality claim documented in-file: boot-anchored,
  unique per live process for a whole boot session (macOS equivalent of
  Linux /proc field-22); it does NOT pin the task the way a pidfd does —
  every consumer pairs it with `getpgid`/`kill(-pgid)` and accepts the
  documented validate-then-kill race (why macOS tree evidence receipts as
  `SAMPLED_TREE`, never `ExactTree`).
- `owned_signal_group` / `owned_signal_group_pinned` /
  `owned_signal_leader_pinned`: gained a `uint64_t identity` parameter.
  Linux branches are character-identical to the old gates (pidfd-present
  behavior byte-identical; the new parameter is `(void)`-cast). Non-Linux
  branches revalidate the recorded start identity when pidfd is absent and
  signal via `kill(-pgid)`/`kill(pid)`.
- `rt_process_owned_cancel`: on non-Linux the registry match on
  (pid, generation, start_identity) is the whole authorization — the
  pidfd>=0 requirement stays Linux-only. All call sites updated (async
  paths remain runtime-ENOTSUP on macOS by design).
- `owned_run_bounded_impl`: Linux-only ENOTSUP gate removed (portable Unix
  body); the pidfd-open gate now tolerates ENOTSUP/EOPNOTSUPP and proceeds
  on start-identity (real open failures other than "unsupported" still fail
  closed); `RtOwnedCleanup` carries `start_identity`; timeout/cancel
  revalidation routed through `owned_identity_revalidated` (Linux: the
  original `owned_pidfd_live && getpgid` expression, unchanged).
- Tree sampling: `RtOwnedTreeSample` shared across Linux/Apple; macOS
  sampler = one `KERN_PROC_ALL` sysctl pass filtered by `e_pgid`, per-member
  resident size via `proc_pid_rusage(2)` (RUSAGE_INFO_V2, V0 fallback).
  io_read/io_write stay 0 on macOS (`ri_diskio_*` would mislabel pager/
  network traffic — counters remain honestly unavailable).
- Direct-child `wait4` rusage sets `RT_PROCESS_EVIDENCE_DIRECT_CHILD_RUSAGE`
  exactly as before; the fill site comment now documents the quality ladder:
  exact process-only leader counters, `SAMPLED_TREE` descendants, io
  unavailable where the platform cannot report it.

### Verification transcript (fresh binary:
### build/cargo-r2/release/simple, built by scripts/setup/build-gpu-seed.shs)

- Standalone strict compile of the C file:
  `cc -std=c11 -D_GNU_SOURCE [-DRT_PROCESS_OWNED_CORE_ONLY / -DRT_PROCESS_OWNED_TESTING / -DRT_PROCESS_OBSERVATION_V4_TESTING …] -Wall -Wextra -Werror -Wpedantic -O2 -pthread -Isrc/runtime -c src/runtime/runtime_process_owned.c`
  → 0 warnings/errors in all 5 define permutations (this check was vacuous
  before the `__unix__` fix — the Unix body never compiled on macOS).
- `sh scripts/setup/build-gpu-seed.shs` →
  `PASS — built …/build/cargo-r2/release/simple (39655176 bytes) with features vulkan,metal,simple-compiler/vulkan-graphics` +
  `PASS — 5 capability probe(s) executed`.
- Acceptance spec (run twice, identical outcomes):

  11 examples / 8 passed / 3 failed:
  - ✓ measures a real owned child tree through the production facade
  - ✓ proves a wall watchdog with a real child
  - ✓ records a real segmentation signal without calling it memory exhaustion
  - ✓ classifies only affirmative termination evidence
  - ✓ proves a memory budget event from scope counters
  - ✗ proves a live Linux memory kill from the delegated service provider
  - ✗ proves a live Linux PID limit from the delegated cgroup counter
  - ✗ records a supervisor-requested external termination
  - ✓ detects a confirmed regression while preserving its approved baseline
  - ✓ detects missing phases and quadratic work before timeout
  - ✓ retains a rare spike and explains incremental invalidation

  The 3 ✗ rows require `/usr/bin/systemd-run` (delegated cgroup provider);
  on macOS they fail closed with `InfrastructureFailure` (signal 0 instead
  of 9/15, no ProcessLimit) — honest unavailability, not fabricated
  evidence. Full logs:
  `build/macos_pidfd_check/spec_cargo_r2_v4.log`, `_v5.log` (workspace build
  dir, not committed).
- Direct probes against the fresh binary (logs in build/macos_pidfd_check/):
  `probe_fields` shows `evidence_flags=9` (DIRECT_CHILD_RUSAGE|SAMPLED_TREE),
  exit 0, reaped 1, runtime_error 0 for a normal child; the SEGV fixture
  receipts exit 139 / signal 11 with `rerr=0`; the python-tree fixture
  through `run_in_execution_resource_scope` receipts rss≈42MB, tree≈52MB,
  pids_peak=2, quality=SampledTree.
- Todo unblock item 4 (kill/wait paths reject `pid <= 0`): every signal
  helper's first statement is `pid <= 0 → ESTALE` on all platforms;
  unsupported counters (io on macOS) remain 0/Unavailable by construction.

### Follow-ups / notes

- **Linux re-verification**: the pidfd paths were kept byte-identical by
  construction but were NOT re-run on a Linux host in this sweep (the
  designated Linux qualification lane should re-run this spec there; the 3
  systemd rows should flip to green on a systemd host).
- The runtime-process selfcheck link
  (`scripts/check/check-mci-v2-process-safety.shs` fixtures) still does not
  link on macOS — pre-existing, now failing on a different (larger) set of
  runtime.c array symbols because the Unix section finally compiles on
  macOS. The v3/pov4 value surface was never CORE_ONLY-fenced; that is a
  harness gap, not a runtime defect.
- Also rebuilt (same source, standard cargo default dir):
  `src/compiler_rust/target/release/simple` — same code, same behavior;
  nothing deploys from there.
- Not committed (per sweep constraints); worktree files touched:
  `src/runtime/runtime_process_owned.c`,
  `src/lib/nogc_sync_mut/io/resource_scope.spl`,
  `test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl`
  (decorator→comment normalization), this todo.

---

# macOS Process-Group Resource Receipt

Status: blocked pending a prepared macOS qualification host.

Owner: runtime/process provider maintainer.

Current source boundary: macOS has process-group/RLIMIT enforcement and legacy bounded execution, but the owned observed provider currently requires Linux pidfds and degrades to `ResourceEvidenceQuality.Unavailable`. Direct-child `ru_maxrss` byte semantics are already handled in the Unix receipt code.

Unblock work:

1. Permit the owned slot lifecycle to use start-identity plus `wait4`/`killpg` when pidfds are unavailable.
2. Retain direct-child CPU/max-RSS and sample descendant processes with documented process-only/sampled-tree quality.
3. Run direct-child, descendant, timeout, signal, and external-cancel fixtures on macOS.
4. Confirm every kill/wait path rejects `pid <= 0` and that unsupported counters remain unavailable.

Resume command on the macOS host: build the source-matched runtime and run `bin/simple test test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl` with the macOS platform rows enabled.
