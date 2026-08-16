# Browser renderer jail confines a compromised renderer

Mirrored scenario manual for
`test/03_system/browser_engine/browser_renderer_sandbox_spec.spl`.

| Field | Value |
| --- | --- |
| Requirement | REQ-WEB-BROWSER-014 sandbox/broker |
| Cases | SANDBOX-N, SANDBOX-E, SANDBOX-D |
| Category | security |
| Gate | `sh scripts/check/check-browser-renderer-sandbox-seccomp.shs` |
| Executable spec | `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl` |
| Runtime status | **Not executed** — no admitted pure-Simple runtime on this host |

## Scenario: keeps allow-listed I/O working while killing a non-allow-listed syscall

A renderer process is confined before it parses any untrusted page. The
operator needs two opposite guarantees at once: the renderer must still do its
job (read the page bytes handed to it, write pixels back), and it must lose the
ability to reach anything else — no new sockets, no matter what the page does
to it. This scenario proves both halves against the real jail, plus the honest
third case where the host kernel cannot provide the jail at all.

### Steps

1. **Enter the real browser renderer jail via `rt_browser_renderer_sandbox_enter`.**
   The gate builds and runs
   `src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`, which
   forks a child that enters the real jail. The preinit contract is simulated
   faithfully: `argv[0]` is the marker, `envp` is empty, and only fds 0..3 are
   held. This is not a mock and not a source-text assertion.

2. **SANDBOX-N — allow-listed read/write on inherited pipe fds still succeed
   inside the jail.** Confinement that also breaks the renderer's own job is
   not a usable sandbox, so the normal path is asserted first.

3. **SANDBOX-E — a non-allow-listed `socket()` is killed by
   `SECCOMP_RET_KILL_PROCESS`, not merely denied.** This is the discriminating
   assertion. The pre-2026-08-15 filter was a *deny-list* defaulting to
   `SECCOMP_RET_ALLOW`, so an unlisted syscall — including any future kernel
   addition — was permitted, and a denied one merely returned `EPERM` with the
   child surviving. The allow-list contract is that the child dies with
   `SIGSYS`. A deny-list regression therefore fails this step rather than
   passing it quietly.

4. **SANDBOX-D — the verdict states how many checks actually ran.** A kernel
   without seccomp/Landlock, or a host with no C compiler, means the jail was
   never entered. The gate reports `ERROR — nothing was checked` (exit 2) in
   both cases and the spec fails. An unexercised property is never a pass.

### Verdict contract

The gate's verdict is the last line of stdout:

| Verdict | Exit | Meaning |
| --- | --- | --- |
| `PASS — 3 check(s) verified: ...` | 0 | jail entered, both directions proven |
| `FAIL — ...` | 1 | the jail did not behave as specified |
| `ERROR — nothing was checked: ...` | 2 | jail never entered; not a pass |

## Evidence status

The gate itself was executed on this host and reported
`PASS — 3 check(s) verified`, including a real `SIGSYS` kill on `socket()`.
That is **native C-runtime evidence for the jail**, and it is what closes the
gap left when the self-check landed on 2026-08-15 wired to no runner.

The **SSpec scenario above has not been executed**: this host has no admitted
pure-Simple self-hosted runtime (see
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`
and the bootstrap admission blocker recorded in the lane state). Rust-seed
output is not accepted as evidence for this lane. The spec is written to
execute unchanged once a qualified runtime is deployed; until then
REQ-WEB-BROWSER-014 remains **not promoted**.
