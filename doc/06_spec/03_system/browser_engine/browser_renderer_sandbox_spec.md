# browser_renderer_sandbox_spec

> A renderer process is confined before it parses any untrusted page.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_renderer_sandbox_spec

A renderer process is confined before it parses any untrusted page.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A renderer process is confined before it parses any untrusted page.
        The operator needs two opposite guarantees at once: the renderer must
        still do its job (read the page bytes handed to it, write pixels back),
        and it must lose the ability to reach anything else — no new sockets,
        no matter what the page does to it. This scenario proves both halves
        against the real jail, plus the honest third case where the host
        kernel cannot provide the jail at all.

## Scenarios

### browser renderer jail confines a compromised renderer

#### keeps allow-listed I/O working while killing a non-allow-listed syscall

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps allow-listed I/O working while killing a non-allow-listed syscall
- Enter the real browser renderer jail via rt_browser_renderer_sandbox_enter
- SANDBOX-N: allow-listed read/write on inherited pipe fds still succeed inside the jail
   - Expected: code equals `0`
- SANDBOX-E: a non-allow-listed socket() is killed by SECCOMP_RET_KILL_PROCESS, not merely denied
- SANDBOX-D: the namespace posture is published and matches the observed /proc/self/ns/net identity
- SANDBOX startup failure: the jail refuses to start on a contract violation, and never starts silently
- The verdict states how many checks actually ran, so an unexercised jail cannot read as a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps allow-listed I/O working while killing a non-allow-listed syscall")
"""
A renderer process is confined before it parses any untrusted page.
The operator needs two opposite guarantees at once: the renderer must
still do its job (read the page bytes handed to it, write pixels back),
and it must lose the ability to reach anything else — no new sockets,
no matter what the page does to it. This scenario proves both halves
against the real jail, plus the honest third case where the host
kernel cannot provide the jail at all.
"""
step("Enter the real browser renderer jail via rt_browser_renderer_sandbox_enter")
val (stdout, stderr, code) = process_run("sh", [SANDBOX_GATE])

step("SANDBOX-N: allow-listed read/write on inherited pipe fds still succeed inside the jail")
expect(code).to_equal(0)
expect(stdout).to_contain("rt_browser_renderer_seccomp_allowlist_selfcheck: PASS")

step("SANDBOX-E: a non-allow-listed socket() is killed by SECCOMP_RET_KILL_PROCESS, not merely denied")
# An EPERM-style deny-list would let the child survive the call. The
# allow-list contract is that the process dies with SIGSYS instead.
expect(stdout).to_contain("SIGSYS-killed by SECCOMP_RET_KILL_PROCESS")

step("SANDBOX-D: the namespace posture is published and matches the observed /proc/self/ns/net identity")
# The namespace layer removes the renderer's route to the network
# instead of relying on every socket-creating syscall staying denied.
# It is REPORTED, never assumed: the self-check fails if the posture
# bit claims isolation while the net-namespace identity is unchanged.
# Both postures are legitimate results, so assert the key is present
# rather than pinning one value — a host with
# kernel.apparmor_restrict_unprivileged_userns=1 (Ubuntu 24.04 default)
# honestly reports `unavailable`, and that must not read as failure.
expect(stdout).to_contain("sandbox_namespaces=")

step("SANDBOX startup failure: the jail refuses to start on a contract violation, and never starts silently")
# The three assertions above all describe a jail that is already UP.
# This one describes what happens when it must NOT come up: a renderer
# worker handed a non-empty environment must die with exit 126 rather
# than inherit its parent's environment, and
# rt_browser_renderer_sandbox_enter must return false rather than
# report a jail it never built. Both arms fire before any kernel
# capability is consulted, so unlike the checks above they can never
# SKIP — a host without seccomp still decides them.
expect(stdout).to_contain(
    "rt_browser_renderer_startup_failure_selfcheck: PASS")
expect(stdout).to_contain("a non-empty envp is refused with exit 126")

step("The verdict states how many checks actually ran, so an unexercised jail cannot read as a pass")
# ERROR (exit 2) covers a kernel lacking seccomp/Landlock and a host
# with no C compiler. Both mean the jail was never entered, and both
# are already excluded by the exit-0 check above. Asserting the counted
# verdict closes the remaining gap: a vacuous run that verified nothing
# cannot satisfy this, because the count is ACCUMULATED as each
# self-check passes rather than printed as a literal — an earlier
# revision hardcoded "4 check(s)", which would have kept claiming four
# even if a check were deleted.
expect(stdout).to_contain("PASS — 6 check(s) verified")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b2ee0a54faff2872baee8f52d6105091f4885e53c7906809d899c9a51aa4d8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b2ee0a54faff2872baee8f52d6105091f4885e53c7906809d899c9a51aa4d8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b2ee0a54faff2872baee8f52d6105091f4885e53c7906809d899c9a51aa4d8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/browser_engine/browser_renderer_sandbox_spec.spl
mirror: doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/browser_engine/browser_renderer_sandbox_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/browser_renderer_sandbox_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps allow-listed I/O working while killing a non-allow-listed syscall' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
