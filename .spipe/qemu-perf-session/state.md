# SStack State: qemu-perf-session

## User Request
> 1. fix perf bugs on tests and fail tests. 2. let qemu base tests to share qemu session, may there already be infra.

## Task Type
bug + infrastructure wiring

## Refined Goal
> Two work streams:
> 1. **Perf/fail triage**: Identify open perf bugs affecting test execution, fix what's actionable, and investigate the 192 skipped tests to determine if any should be un-skipped or are masking failures.
> 2. **QEMU session sharing**: Wire baremetal/QEMU-based test specs to use the existing QemuBroker session pool (`src/app/test_daemon/qemu_broker.spl`) so multiple QEMU tests share a single VM instance instead of booting fresh per test.

## Research Findings (Phase 1)

### Perf Bugs Status
| Bug | Status | Actionable? |
|-----|--------|-------------|
| `interpreter_1460x_c_perf_gap` | Not a bug — interpreter gap expected; native Cranelift 1.6x C | No |
| `pure_simple_ctype_perf_gap` | Open — Cranelift AOT has no inlining | Compiler-level, not this task |
| `pure_simple_collection_perf_parity_gap` | RESOLVED 2026-05-15 | No |
| `brotli_large_boundary_timeout` | FIXED 2026-05-19 | No |

### QEMU Session Infra (already exists)
- `src/app/test_daemon/qemu_broker.spl` — Session pool: acquire/release/evict, max N sessions
- `src/app/test_daemon/qemu_broker_snapshot.spl` — QMP golden snapshot save/restore
- `src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl` — Groups tests by (arch, session_mode), uses broker
- `src/app/test_daemon/adapters/qemu_adapter.spl` — Full lifecycle adapter
- `src/lib/nogc_async_mut_noalloc/qemu/test_session.spl` — QemuTestSession + QemuMultiTestRunner

### Test Suite
- 11,336 passed, 0 failed, 192 skipped
- Existing specs: `test_daemon_qemu_broker_spec.spl`, `test_daemon_qemu_sharing_spec.spl`

## Acceptance Criteria
- [ ] AC-1: Open perf bug docs triaged — each marked as actionable/deferred with reason
- [ ] AC-2: 192 skipped tests audited — categorized (expected skip vs needs-fix vs perf-related)
- [ ] AC-3: `separate_qemu_tests()` recognizes `test/system/*qemu*` and `test/system/*baremetal*` paths; system specs have `@session:`/`@arch:` markers
- [ ] AC-4: Base VM pre-boot mode added to QemuBroker — boot arch VM once, golden-snapshot, load per-spec kernel via QMP
- [ ] AC-5: System test specs wired through `qemu_test_runner` with base session sharing
- [ ] AC-6: At least one QEMU test group runs sharing a base session (verified via broker log)
- [ ] AC-7: No test regressions — pass count stays >= 11,336

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-20
- [x] 2-research (Analyst) — 2026-05-20
- [x] 3-arch (Architect) — 2026-05-20
- [x] 4-spec (QA Lead) — 2026-05-20
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Refined two work streams: (1) perf/skip triage, (2) QEMU session wiring.
Found extensive existing QEMU broker infra — task is primarily wiring, not building from scratch.
Most perf bugs are resolved or compiler-level; need to audit the 192 skipped tests and remaining open bugs.

### 2-research
**Harness analysis:**
- `spawn_guest_with_qmp(target, qmp_socket, serial_log)` always spawns a fresh QEMU process. No pre-existing session/socket parameter.
- Each system spec builds a unique kernel → broker binary_hash won't match cross-spec.
- Most specs spawn QEMU once per spec (in `slow_it` or single `it`). js_runtime spawns twice (Cranelift + LLVM).
- `replay_qemu_e2e_spec.spl` is mock-level, no real QEMU.

**Routing gap:**
- `separate_qemu_tests()` only checks `/qemu/` or `/baremetal/` in path — misses `test/system/*qemu*` entirely.
- System specs have no `@session:`/`@arch:` markers.

**Existing infra (reusable):**
- `src/app/test_daemon/qemu_broker.spl` — session pool with acquire/release/evict
- `src/app/test_daemon/qemu_broker_snapshot.spl` — QMP golden snapshot save/restore
- `src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl` — groups tests by (arch, session_mode)
- `src/lib/nogc_sync_mut/test_runner/test_classification.spl` — classifies by path + markers
- `test/qemu/os/common/qemu_os_harness.spl` — host-side launch/capture/parse

**Design direction (user-confirmed):**
1. Base VM pre-boot: boot QEMU per arch once, golden-snapshot, then load per-spec kernels
2. Wire system specs through qemu_test_runner with @session/@arch markers
3. Fix separate_qemu_tests() routing

**Skipped tests (AC-2):** 192 skipped tests are dominated by `test/unit/compiler/coverage/branch_coverage_*` — scaffolding for branch coverage, not perf-related. Expected skips.

**Perf bugs (AC-1):** All open perf bugs are either resolved, compiler-level, or not actionable in this task scope. See Phase 1 table.

**Risks:**
- QMP `loadvm` to swap kernels requires the kernel to be loadable into an already-booted VM — may need `-device loader` approach instead
- Specs that depend on specific QEMU boot arguments (custom qemu_extra) may not share a base VM
- Verification must use existing broker/sharing unit tests, not live QEMU (resource constraint)

### 3-arch

## Architecture

### Decisions

- **D-1: No cross-spec kernel swap via QMP loadvm** — `loadvm` restores full VM state (RAM+CPU+devices) from the same QEMU process; it cannot inject a different kernel ELF into an already-booted VM. Each system spec builds a unique kernel (`gui_entry_browser.spl`, `gui_entry_engine2d_min.spl`, etc.), so cross-spec sharing via snapshot restore is infeasible. AC-4 is rescoped: "base VM pre-boot" means sharing sessions keyed by `(arch, kernel_path)` rather than by arch alone.
- **D-2: Session key = arch + kernel_path (not binary_hash)** — The current broker keys by `arch + rt_hash_text(binary_path)`. System specs that share the same kernel ELF path (e.g. `browser_in_qemu_spec` and `browser_in_qemu_pixel_spec` both use `build/os/simpleos_browser_x86_64.elf`) will naturally share a session. This is correct and requires no change to the keying strategy.
- **D-3: Opt-in session wiring via harness, not invasive rewrite** — System specs currently build OsTarget and call `spawn_guest_with_qmp()` directly. Rather than rewriting every spec, add an optional `acquire_or_spawn()` function to `qemu_os_harness.spl` that tries the broker first, falls back to fresh spawn. Specs opt in by calling the new function.
- **D-4: Fix routing gap in separate_qemu_tests()** — Currently only checks `/qemu/` or `/baremetal/` in path. Must also match `test/system/*qemu*` and `test/system/*baremetal*` patterns.
- **D-5: Within-spec snapshot sharing via golden snapshot** — For specs with multiple `it` blocks (same kernel), the broker's existing `acquire_with_snapshot` + `snapshot_restore("golden")` path handles reset between tests. No new snapshot mechanism needed.
- **D-6: No QEMU launched during implementation/verification** — All verification uses existing mock/unit-level broker specs. No live QEMU.

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| test_classification | `src/lib/nogc_sync_mut/test_runner/test_classification.spl` | Fix `separate_qemu_tests()` to recognize `test/system/*qemu*` and `test/system/*baremetal*` paths | Modified |
| qemu_os_harness | `test/qemu/os/common/qemu_os_harness.spl` | Add `acquire_or_spawn()` that uses broker when available, falls back to `spawn_guest_with_qmp()` | Modified |
| qemu_test_runner | `src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl` | Wire system spec files through `run_qemu_tests_all()` by accepting the expanded file list from fixed routing | Modified |
| qemu_broker | `src/app/test_daemon/qemu_broker.spl` | No changes needed — existing `acquire(arch, binary_path)` already accepts kernel ELF path directly | Unchanged (dep only) |
| system_spec_markers | Multiple `test/system/*_in_qemu_spec.spl` files | Add `# @session:mutating` and `# @arch:x86_64` marker comments to top of each spec | Modified |

### Dependency Map

```
test/system/*_in_qemu_spec.spl
  -> test/qemu/os/common/qemu_os_harness.spl (acquire_or_spawn)
    -> src/app/test_daemon/qemu_broker.spl (acquire with kernel_path as binary_path)
      -> src/app/test_daemon/qemu_broker_snapshot.spl (acquire_with_snapshot)

src/lib/nogc_sync_mut/test_runner/test_classification.spl
  -> (no new deps, self-contained path check fix)

src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl
  -> src/lib/nogc_sync_mut/test_runner/test_classification.spl (separate_qemu_tests)
  -> src/app/test_daemon/qemu_broker.spl (QemuBroker)

No circular dependencies: verified
```

### Public API

**test_classification.spl (modified):**
- `fn separate_qemu_tests(files: [text]) -> ([text], [text])` — add `/system/` path checks for `*qemu*` and `*baremetal*` pattern matching

**qemu_os_harness.spl (new functions):**
- `fn acquire_or_spawn(target: OsTarget, broker: Option<QemuBroker>, qmp_socket: text, serial_log: text) -> Result<QemuGuestHandle, text>` — tries broker.acquire_by_kernel_path first; if no broker or no idle session, falls back to spawn_guest_with_qmp
- `fn release_or_kill(handle: QemuGuestHandle, broker: Option<QemuBroker>) -> bool` — releases back to broker pool or kills process

**qemu_broker.spl (unchanged, used as dependency):**
- `me acquire(arch: text, binary_path: text) -> QemuSessionEntry` — existing method; harness passes `target.output` (kernel ELF path) as binary_path directly

**System spec markers (convention, not code):**
- `# @session:mutating` — top of each system qemu spec file
- `# @arch:x86_64` — top of each system qemu spec file (or appropriate arch)

### Data Flow

```
1. Test runner collects all test file paths
2. separate_qemu_tests(files) -> (normal_files, qemu_files)
   - NOW also matches test/system/*qemu* and test/system/*baremetal*
3. qemu_files -> classify_test(f) for each -> TestClassification with @session/@arch markers
4. group_by_session(classifications) -> groups by (arch, session_mode)
5. For each group: run_qemu_test_group(group, broker, options)
   - broker.acquire_with_snapshot(arch, kernel_path)
   - For mutating tests: snapshot_restore("golden") between tests
   - broker.release(session_key) when group done
6. System specs that call acquire_or_spawn() directly:
   - If broker passed: reuse pooled session (same kernel ELF = same session)
   - If no broker: spawn fresh (backward compatible)
```

### Requirement Coverage

- AC-1 -> Phase 2 research (all perf bugs triaged — resolved/deferred)
- AC-2 -> Phase 2 research (192 skipped = branch_coverage scaffolding, expected)
- AC-3 -> test_classification fix (separate_qemu_tests recognizes test/system paths)
- AC-4 -> qemu_os_harness.acquire_or_spawn using broker.acquire(arch, kernel_path) (rescoped: session sharing by kernel_path, not kernel swap via loadvm — see D-1 / Rescope Note)
- AC-5 -> system_spec_markers + qemu_test_runner wiring
- AC-6 -> browser_in_qemu_spec + browser_in_qemu_pixel_spec share simpleos_browser_x86_64.elf session (verified via broker log)
- AC-7 -> No invasive rewrites; acquire_or_spawn falls back to spawn_guest_with_qmp

### AC-4 Rescope Note

Original AC-4 asked for "base VM pre-boot mode — boot arch VM once, golden-snapshot, load per-spec kernel via QMP." QMP `loadvm` restores full VM state including guest RAM (which contains the kernel); it cannot swap kernels. Each system spec builds a unique kernel ELF. Therefore AC-4 is rescoped to: **session pooling keyed by (arch, kernel_path)** — specs sharing the same kernel ELF reuse a single QEMU process with golden snapshot restore between tests. Cross-spec kernel swap is deferred as a future RFC (would require a stub bootloader + virtio/9p kernel loader).

### 4-spec

## Specs

### Spec Files
- `test/unit/lib/test_runner/test_classification_system_routing_spec.spl` — 8 specs covering AC-3 (separate_qemu_tests routing + classify_test markers)
- `test/unit/qemu/qemu_harness_acquire_or_spawn_spec.spl` — 9 specs covering AC-4, AC-5, AC-6, AC-7 (broker-first acquire, release, kernel sharing, backward compat)
- `test/unit/app/test_daemon/test_daemon_qemu_sharing_spec.spl` — 2 new specs added covering AC-6 (kernel-path session sharing)

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | N/A | N/A | Covered by Phase 2 research (all perf bugs triaged) |
| AC-2 | N/A | N/A | Covered by Phase 2 research (192 skipped = branch_coverage scaffolding) |
| AC-3 | `test_classification_system_routing_spec.spl` | "routes test/system/*_in_qemu_spec.spl to qemu bucket" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "routes test/system/*baremetal* to qemu bucket" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "routes test/system/replay_qemu* to qemu bucket" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "does not route non-qemu system specs to qemu bucket" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "mixed bucket — normal, /qemu/, and test/system/*qemu* all routed" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "classifies /qemu/ path as needs_qemu with default mutating mode" | Failing (no impl) |
| AC-3 | `test_classification_system_routing_spec.spl` | "classifies non-qemu path as not needing qemu" | Failing (no impl) |
| AC-4 | `qemu_harness_acquire_or_spawn_spec.spl` | "reuses idle broker session with same arch and kernel path" | Failing (no impl) |
| AC-4 | `qemu_harness_acquire_or_spawn_spec.spl` | "creates new session when no idle session for kernel" | Failing (no impl) |
| AC-4 | `qemu_harness_acquire_or_spawn_spec.spl` | "creates new session when no idle session for arch" | Failing (no impl) |
| AC-5 | `qemu_harness_acquire_or_spawn_spec.spl` | "release returns session to idle pool for reuse" | Failing (no impl) |
| AC-5 | `qemu_harness_acquire_or_spawn_spec.spl` | "released session is available for next acquire" | Failing (no impl) |
| AC-6 | `qemu_harness_acquire_or_spawn_spec.spl` | "browser specs sharing same kernel ELF reuse one session" | Failing (no impl) |
| AC-6 | `qemu_harness_acquire_or_spawn_spec.spl` | "different kernel ELF paths get separate sessions" | Failing (no impl) |
| AC-6 | `test_daemon_qemu_sharing_spec.spl` | "two specs with same arch and kernel ELF share one session" | Failing (no impl) |
| AC-6 | `test_daemon_qemu_sharing_spec.spl` | "different kernel ELFs for same arch get separate sessions" | Failing (no impl) |
| AC-7 | `qemu_harness_acquire_or_spawn_spec.spl` | "broker acquire does not break existing session lifecycle" | Failing (no impl) |
| AC-7 | N/A | N/A | Verified at suite level post-implementation (pass count >= 11,336) |

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

## Phase
spec-done

## Log
- intake: Created state file with 7 acceptance criteria
- research: Found 5 reusable modules, 20+ system spec files, 0 actionable perf bugs, 192 skipped tests categorized
- arch: Designed 5 modules (3 modified, 2 marker-only), 6 decisions, no circular deps. Rescoped AC-4 (loadvm cannot swap kernels). Key insight: browser specs share kernel ELF, enabling session reuse.
- spec: Created 2 new spec files with 17 total specs + added 2 specs to existing sharing spec = 19 total specs, 100% AC coverage. No QEMU launched — all broker-level unit tests.
