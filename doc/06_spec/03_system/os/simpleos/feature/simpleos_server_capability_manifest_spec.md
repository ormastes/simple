# Honest SimpleOS server protocol discovery

> Operators inspect one production-owned capability projection before publishing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Honest SimpleOS server protocol discovery

Operators inspect one production-owned capability projection before publishing

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Operators inspect one production-owned capability projection before publishing
or negotiating server protocols. The same projection keeps unavailable modern
web transports closed and distinguishes SSH from its authenticated SFTP
subsystem.

## Scenarios

### REQ-013: publish only reachable web protocols

#### should publish the probed HTTP/1.1 and HTTP/2 production owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


**Scenario capture:** protocol after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-013
# @req REQ-015
# @req REQ-016
```

</details>

#### should reject unavailable HTTP/3 QUIC and WebTransport negotiations

- should reject unavailable HTTP/3 QUIC and WebTransport negotiations
- Offer unavailable and unknown ALPN identifiers to the canonical negotiation policy
   - Expected: simpleos_http_select_alpn("h3") equals ``
   - Expected: simpleos_http_select_alpn("quic") equals ``
   - Expected: simpleos_http_select_alpn("webtransport") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unavailable HTTP/3 QUIC and WebTransport negotiations")
step("Offer unavailable and unknown ALPN identifiers to the canonical negotiation policy")
expect(simpleos_http_select_alpn("h3")).to_equal("")
expect(simpleos_http_select_alpn("quic")).to_equal("")
expect(simpleos_http_select_alpn("webtransport")).to_equal("")
```

</details>

### REQ-015 and REQ-016: publish SSH and SFTP from their reachable owners

#### should publish SSH only after live authentication and keep SFTP unpublished without atomic VFS authority

- should publish SSH only after live authentication and keep SFTP unpublished without atomic VFS authority
   - Protocol capture: after_step
- Authenticate, open a channel, and request SFTP through the canonical daemon
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: simpleos_ssh_capability_manifests(false, true, "listener", "session").len() equals `0`
   - Expected: simpleos_ssh_capability_manifests(true, false, "listener", "session").len() equals `1`
- Refuse to promote subsystem framing while per-principal atomic VFS authority is absent
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: simpleos_ssh_capability_manifests(true, false, "authenticated-channel", "sftp-vfs-blocked").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish SSH only after live authentication and keep SFTP unpublished without atomic VFS authority")
step("Authenticate, open a channel, and request SFTP through the canonical daemon")
expect(simpleos_ssh_capability_manifests(false, true, "listener", "session").len()).to_equal(0)
expect(simpleos_ssh_capability_manifests(true, false, "listener", "session").len()).to_equal(1)
step("Refuse to promote subsystem framing while per-principal atomic VFS authority is absent")
expect(simpleos_ssh_capability_manifests(true, false, "authenticated-channel", "sftp-vfs-blocked").len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-013`
- `REQ-015`
- `REQ-016`
- `REQ-016:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99abf5a64f2cc07db05ea6732caeebdb923e4746713f59bfd55842c4d718b6e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99abf5a64f2cc07db05ea6732caeebdb923e4746713f59bfd55842c4d718b6e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99abf5a64f2cc07db05ea6732caeebdb923e4746713f59bfd55842c4d718b6e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should publish the probed HTTP/1.1 and HTTP/2 production owners' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish the probed HTTP/1.1 and HTTP/2 production owners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unavailable HTTP/3 QUIC and WebTransport negotiations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unavailable HTTP/3 QUIC and WebTransport negotiations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish SSH only after live authentication and keep SFTP unpublished without atomic VFS authority' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_server_capability_manifest_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should publish SSH only after live authentication and keep SFTP unpublished without atomic VFS authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
