# RV64 Sv39, PID1, Network, SSH, and WM QEMU Completion Plan

## Goal

Prove, from current source in one fail-closed QEMU lane, that SimpleOS RV64
activates Sv39, creates and retains PID 1, brings VirtIO network TX/RX online,
serves production OpenSSH authentication and filesystem-backed commands, and
presents a process-owned WM frame in that order.

The executable scenario is
`test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`. Evidence lives under
`build/os/rv64-ssh-live/`; the mirrored operator manual belongs at
`doc/06_spec/03_system/os/rv64_ssh_live_login_in_qemu_spec.md`.

## Non-Negotiable Evidence Contract

The ordered runtime receipts are:

1. `sv39-active` — emitted only after SATP mode readback is Sv39.
2. `pid1-live` — emitted only after the process owner creates PID 1 and a
   liveness query confirms it remains owned.
3. `network-tx-ready`, `network-rx-ready`, `network-service-ready` — derived
   from the existing VirtIO operations, not synthesized markers.
4. `sshd-ready` — emitted by the production daemon after bind/listen.
5. `sshd-session-complete` and `sshd-accept-resumed` — correlated per real
   OpenSSH connection.
6. `wm-process-owned-frame-ready` — emitted only when a live process identity
   and its correlated compositor-present receipt both exist.
7. One terminal `TEST PASSED`, emitted by the host evidence owner after every
   receipt and OpenSSH oracle passes.

Missing, duplicate, or reordered receipts fail. Banner-only SSH, canned command
output, marker-only PID1, fixed rectangles, Rust-seed tests, Stage 2 tools, and
stale artifacts are diagnostics, never PASS evidence.

## Shared Interfaces and Manual Vocabulary

- Pure state machine: `Rv64BootGateState`, `rv64_boot_gate_advance`,
  `rv64_boot_gate_verdict`.
- Fixture/checker helpers: `prepare_rv64_boot_gate_fixture`,
  `check_rv64_boot_gate_transcript`.
- Manual steps:
  - `step("Build admitted RV64 boot image")`
  - `step("Boot QEMU and capture ordered lifecycle receipts")`
  - `step("Prove OpenSSH login, exec, rejection, and accept-loop recovery")`
  - `step("Prove process-owned WM readiness")`
- Any scaffold must call `assert(false)` or `fail(...)` until its real oracle
  exists. Silent no-op and placeholder passes are forbidden.

## Current Authoritative Blockers

| Blocker | Evidence | Unblock condition |
|---|---|---|
| Stage 3 self-host crashes after HIR | `doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`; retained log ends in MIR method-call lowering around `method_calls_literals.spl:2366-2403,2542-2695,2961+` with corrupt receiver local `103079215111` | Exact backtrace/localization, pure-Simple fix, exact native regression plus adjacent aggregate/method-call case |
| No admissible Stage 4 CLI | `bin/simple` absent; no essential-tools receipt | `--full-cli --deploy` plus the exact fresh binary passing `check-bootstrap-essential-tools-smoke.shs` |
| SSH entry has no Sv39/PID1 owner | `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl:40-73`; noalloc handoff/services at `src/os/kernel/boot/riscv_noalloc_handoff.spl:84-108` and `riscv_noalloc_services.spl:32-48` | SATP readback and process-owner PID1 create/liveness integrated before network/SSHD |
| Actual PID1 owner is disconnected | `src/os/services/pm_service.spl:264-271` | Boot orchestrator calls the process owner and consumes its liveness result |
| RV64 SSH probe uses fixed-command behavior | `src/os/ssh_qemu_contract.spl:74-120`; canned combined command at `src/os/apps/sshd/ssh_session_channel.spl:244-250`; fixed outputs at `ssh_session.spl:325-331` | Separate real OpenSSH commands execute target filesystem payloads and stream actual stdout/status |
| Desktop proof is a fixture/shim | Fixed rectangles at `desktop_service_entry.spl:43-81`, string-only GUI stub at `boot/baremetal_stubs.c:790-803`, banner shim at `desktop_service_entry.spl:176-183`, unconditional ready/PASS at `:210-220` | PID-owned WM process plus correlated compositor presentation; failures return before readiness |
| SSpec/manual are legacy and stale | Spec `:179-347` lacks state-machine negatives/manual steps; manual says guest port 22 while source asserts 2222 and reports stale KEX-only status | Rewrite manual-first SSpec, generate one canonical mirror, review all seven maintain scores and traceability |

## Acceptance and Evidence Matrix

No row is complete until the Evidence cell contains one fresh passing result.

| AC | Required gate | Current status | Retained evidence | Owner | Final reviewer |
|---|---|---|---|---|---|
| AC-1 | Claim/reproduce Stage 3 failure; pure-Simple root fix; exact + adjacent native regression | BLOCKED | bug record, bounded diagnostic log, backtrace, two regression outputs | bootstrap sidecar | root highest-capability review |
| AC-2 | Provenance Stage 4 CLI and essential test/lint/duplicate/aggregate markers | BLOCKED | Stage 3/4 manifests, hashes, build logs, essential-tools env/log | bootstrap sidecar | root |
| AC-3 | Ordered Sv39/PID1/TX/RX/network/SSHD/WM state machine; missing/reordered/duplicate negatives | NOT IMPLEMENTED | focused unit/system result and transcript checker output | RV64 gate sidecar | root |
| AC-4 | Real OpenSSH good auth; `true`; `simple --version`; `simple.smf --version`; bad auth; accept resumes after each session | NOT IMPLEMENTED | host transcript, per-command rc/stdout, serial log, correlation IDs | SSH owner | root |
| AC-5 | Live process-owned WM plus correlated presented frame | NOT IMPLEMENTED | PID/liveness receipt, compositor receipt, QMP capture metadata | PM/scheduler + compositor owners | root |
| AC-6 | Shared interfaces and exact/adjacent fail-closed SSpec coverage | NOT IMPLEMENTED | focused SSpec result | RV64 gate sidecar | root |
| AC-7 | Manual-first steps, zero stubs, seven-score maintain review, mirror and requirement traceability | STALE | scan output, preview/rollback record, generated manual | docs/SPipe sidecar | root manual reviewer |
| AC-8 | This plan and dedicated agent-task breakdown complete | PLANNED | plan and `doc/03_plan/agent_tasks/rv64_sv39_pid1_network_ssh_wm_boot.md` | merge owner | root |
| AC-9 | Guide, feature/layer expert wikis, architecture/design and bug records current | IN PROGRESS | changed-doc inventory in `.spipe/.../state.md` | docs sidecar | root |
| AC-10 | Focused/release guards, locked integration, reachability, clean tree, done receipt | BLOCKED on AC-1..9 | command ledger, commit, ancestry proof, done file | merge owner | root |

## Work Packages

### WP-A — Stage 3 root cause and Stage 4 admission

1. In a fresh lane, run one diagnostics-enabled reproducer; do not reuse the
   exhausted three cycles from commit `3c26d1b9c2f`.
2. Capture the next post-HIR backtrace and the final MIR trace around
   `value_struct_layout.spl:78-117` and method-call/push lowering.
3. Fix the pure-Simple owner. The direct `error_count_value` read remains only
   an avoidance until the receiver corruption is explained and regression
   tested.
4. Add exact aggregate-receiver/native regression and one adjacent
   value-struct/method-call regression.
5. Build and deploy Stage 4; bind hashes and provenance; run essential tools.

Exact commands:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=cranelift --deploy --no-mcp --jobs=2 --diagnostics=test
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --deploy
sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/fresh/stage4/simple
```

### WP-B — Pure boot-gate state machine

Create a pure `src/os/` state machine with the frozen names above. It accepts
typed lifecycle observations, enforces exactly-once ordering, records the first
failure, and never performs QEMU/process/file I/O. Direct specs cover happy,
missing, reordered, duplicate, and post-terminal observations.

### WP-C — Production boot ownership

- Paging owner activates and reads back Sv39.
- PM/scheduler owner creates PID 1 and exposes liveness without a marker proxy.
- Existing VirtIO TX/RX/stats results advance network gates.
- Production SSH daemon advances readiness only after bind/listen.
- Boot orchestrator alone composes these results and emits canonical receipts.

### WP-D — Real SSH command execution

Remove the combined `simple.smf --version; simple --check` special case from the
admitted gate path. Resolve and execute target filesystem payloads, stream real
stdout/status, run four separate good sessions plus one bad-password session,
and prove the daemon returns to accept after every completed/rejected session.

### WP-E — Process-owned WM

Launch WM through the process owner, retain PID/liveness, render through the
canonical compositor/Engine2D path, correlate the first presented frame to that
PID, and advance WM readiness only from both facts. Fixed rectangles and the C
string stub may remain in explicitly diagnostic fixtures but are excluded from
the admitted gate.

### WP-F — SSpec, manual, guide, and wiki

Rewrite the scenario with the frozen operator steps and AC traceability. Keep
unavailable live rows `blocked`, never passing through a disabled assertion.
Generate only `doc/06_spec/03_system/os/rv64_ssh_live_login_in_qemu_spec.md`;
remove or redirect the duplicate `doc/06_spec/test/...` mirror after review.
Run `sspec-maintain scan`, inspect all seven component scores, preview any
improvement, apply only a confirmed patch with rollback, regenerate, and read
the result as an operator manual. Update the QEMU guide and feature/layer expert
wikis in the same change.

## Verification Ledger

Run each final command once after its last relevant edit. A failure begins one
fix cycle; stop after three cycles.

| Gate | Exact command | Required evidence |
|---|---|---|
| Stage 4 tools | `sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/fresh/stage4/simple` | four required true markers and binary hash |
| Focused SSpec | `bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` | executed happy + missing/reordered/duplicate cases |
| Manual scan | `bin/simple sspec-maintain scan test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` | seven scores, blockers, stable findings, mirror, REQ traceability |
| Manual generation | `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec --no-index` | zero stubs and reviewed operator flow |
| Source check | `bin/simple check src/os` | PASS |
| Lint | `bin/simple lint <changed .spl files>` | PASS |
| Duplication | `bin/simple duplicate-check src/os --mode token --min-lines 5` | PASS or reviewed owned finding |
| Shortcut exclusion | `rg -n 'simple\.smf --version; simple --check|_exec_success_output_for_command|rt_desktop_pci_boot_tcp_send_ssh_banner|rect_core_draw_rect_filled' <admitted-path-files>` | no admitted-path match |
| Env facade | `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` | PASS/PASS |
| Spec layout | `find doc/06_spec -name '*_spec.spl' | wc -l` | `0` |
| Whole release | `bin/simple test test --whole --mode=interpreter` | final authoritative PASS |
| Live QEMU | `SIMPLE_TEST_TIMEOUT=900 SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential` | ordered receipts, five auth/session outcomes, one terminal PASS |

Live artifacts:

- `build/os/simpleos_riscv64_ssh_live.elf` plus SHA-256.
- `build/os/rv64-ssh-live/serial.log`.
- `build/os/rv64-ssh-live/openssh-good-*.log` and `openssh-bad-auth.log`.
- `build/os/rv64-ssh-live/boot-gate-verdict.env`.
- WM QMP capture and PID/frame correlation metadata under the same directory.

## Cooperative Ownership and Review

| Lane | Scope | Status |
|---|---|---|
| bootstrap sidecar | AC-1/2 audit and implementation | audit complete; implementation open |
| RV64 gate sidecar | AC-3..6 audit and implementation | audit complete; implementation open |
| docs/SPipe sidecar | AC-7..10 audit and documentation | audit complete; docs in progress |
| merge owner | root Codex agent in this detached worktree | active |
| final reviewer | root normal/highest-capability review | plan findings accepted; no implementation done marks accepted |

The final reviewer must inspect source and retained evidence, not sidecar
summaries alone. Broad PASS, exclusions, generated-manual quality, and done
marks remain root-owned.

## Integration and Termination

After all gates pass, commit intentional changes and hold
`/tmp/simple-main-restart12-push.lock` across fetch, linear rebase, push,
post-push fetch, and `git merge-base --is-ancestor HEAD origin/main`. Use
`env -u GH_TOKEN -u GITHUB_TOKEN` for network operations, never force push or
create a branch, and preserve the file-count guard. Leave a clean tree and
write `/tmp/restart12-riscv.done` with `<reachable-hash> PASS` only then.

If three final fix cycles end with a remaining failure, retain every blocked AC,
push a truthful implementation handoff, and write `WARN` only after reachability.
