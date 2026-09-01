# Simpleos Server Protocol Capabilities Specification

> Tests covering SimpleOS production server capability projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Server Protocol Capabilities Specification

## Scenarios

### SimpleOS production server capability projection

#### reports only reachable HTTP/1.1 and HTTP/2 ALPN implementations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports only reachable HTTP/1.1 and HTTP/2 ALPN implementations
   - Expected: simpleos_http_protocol_reachable("http/1.1") is true
   - Expected: simpleos_http_protocol_reachable("h2") is true
   - Expected: simpleos_http_select_alpn("h2") equals `h2`
   - Expected: simpleos_http_select_alpn("http/1.1") equals `http/1.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports only reachable HTTP/1.1 and HTTP/2 ALPN implementations")
expect(simpleos_http_protocol_reachable("http/1.1")).to_equal(true)
expect(simpleos_http_protocol_reachable("h2")).to_equal(true)
expect(simpleos_http_select_alpn("h2")).to_equal("h2")
expect(simpleos_http_select_alpn("http/1.1")).to_equal("http/1.1")
```

</details>

#### fails closed for HTTP/3 QUIC WebTransport WebSocket ALPN and unknown protocols

- fails closed for HTTP/3 QUIC WebTransport WebSocket ALPN and unknown protocols
   - Expected: simpleos_http_select_alpn("h3") equals ``
   - Expected: simpleos_http_select_alpn("quic") equals ``
   - Expected: simpleos_http_select_alpn("webtransport") equals ``
   - Expected: simpleos_http_select_alpn("websocket") equals ``
   - Expected: simpleos_http_select_alpn("future-protocol") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed for HTTP/3 QUIC WebTransport WebSocket ALPN and unknown protocols")
expect(simpleos_http_select_alpn("h3")).to_equal("")
expect(simpleos_http_select_alpn("quic")).to_equal("")
expect(simpleos_http_select_alpn("webtransport")).to_equal("")
expect(simpleos_http_select_alpn("websocket")).to_equal("")
expect(simpleos_http_select_alpn("future-protocol")).to_equal("")
```

</details>

#### binds HTTP manifests to the production probe and evidence identities

- binds HTTP manifests to the production probe and evidence identities
   - Expected: manifests.len() equals `2`
   - Expected: manifests[0].protocol equals `http/1.1`
   - Expected: manifests[1].protocol equals `h2`
   - Expected: manifest_valid(manifests[0]) is true
   - Expected: manifest_valid(manifests[1]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds HTTP manifests to the production probe and evidence identities")
val manifests = simpleos_http_capability_manifests(true, true, true, "loopback-1", "worker-dispatch-1")
expect(manifests.len()).to_equal(2)
expect(manifests[0].protocol).to_equal("http/1.1")
expect(manifests[1].protocol).to_equal("h2")
expect(manifest_valid(manifests[0])).to_equal(true)
expect(manifest_valid(manifests[1])).to_equal(true)
```

</details>

#### does not validate HTTP claims before live identities exist

- does not validate HTTP claims before live identities exist
   - Expected: absent.len() equals `0`
   - Expected: manifests.len() equals `1`
   - Expected: manifest_valid(manifests[0]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not validate HTTP claims before live identities exist")
val absent = simpleos_http_capability_manifests(true, false, false, "tcp-only", "")
expect(absent.len()).to_equal(0)
val manifests = simpleos_http_capability_manifests(true, true, false, "", "")
expect(manifests.len()).to_equal(1)
expect(manifest_valid(manifests[0])).to_equal(false)
```

</details>

#### does not claim TLS or H2 when the configured listener is cleartext

- does not claim TLS or H2 when the configured listener is cleartext
   - Expected: manifests.len() equals `1`
   - Expected: manifests[0].transport equals `tcp`
   - Expected: manifests[0].tls_required is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not claim TLS or H2 when the configured listener is cleartext")
val manifests = simpleos_http_capability_manifests(false, true, false, "http-live", "h1-dispatch")
expect(manifests.len()).to_equal(1)
expect(manifests[0].transport).to_equal("tcp")
expect(manifests[0].tls_required).to_equal(false)
```

</details>

#### reports SSH and authenticated SFTP independently

- reports SSH and authenticated SFTP independently
   - Expected: simpleos_ssh_protocol_reachable("ssh", true, false) is true
   - Expected: simpleos_ssh_protocol_reachable("sftp-v3", true, false) is false
   - Expected: simpleos_ssh_protocol_reachable("sftp-v3", true, true) is true
   - Expected: simpleos_ssh_protocol_reachable("scp", true, true) is false
   - Expected: ssh_only.len() equals `1`
   - Expected: ssh_only[0].protocol equals `ssh`
   - Expected: with_sftp.len() equals `2`
   - Expected: with_sftp[1].protocol equals `sftp-v3`
   - Expected: manifest_valid(with_sftp[1]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports SSH and authenticated SFTP independently")
expect(simpleos_ssh_protocol_reachable("ssh", true, false)).to_equal(true)
expect(simpleos_ssh_protocol_reachable("sftp-v3", true, false)).to_equal(false)
expect(simpleos_ssh_protocol_reachable("sftp-v3", true, true)).to_equal(true)
expect(simpleos_ssh_protocol_reachable("scp", true, true)).to_equal(false)
val ssh_only = simpleos_ssh_capability_manifests(true, false, "listener-1", "session-1")
expect(ssh_only.len()).to_equal(1)
expect(ssh_only[0].protocol).to_equal("ssh")
val with_sftp = simpleos_ssh_capability_manifests(true, true, "listener-1", "session-1")
expect(with_sftp.len()).to_equal(2)
expect(with_sftp[1].protocol).to_equal("sftp-v3")
expect(manifest_valid(with_sftp[1])).to_equal(true)
```

</details>

#### reports no SSH capabilities before the daemon is ready

- reports no SSH capabilities before the daemon is ready
   - Expected: simpleos_ssh_capability_manifests(false, true, "listener-1", "session-1").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports no SSH capabilities before the daemon is ready")
expect(simpleos_ssh_capability_manifests(false, true, "listener-1", "session-1").len()).to_equal(0)
```

</details>

#### rejects stale and replayed SSH evidence handles

- rejects stale and replayed SSH evidence handles
   - Expected: server_protocol_probe_handle_admitted(handle, 7, 11, "probe-owner-7", 0) is true
   - Expected: server_protocol_probe_handle_admitted(handle, 8, 11, "probe-owner-7", 0) is false
   - Expected: server_protocol_probe_handle_admitted(handle, 7, 11, "probe-owner-7", 11) is false
   - Expected: server_protocol_probe_handle_admitted(handle, 7, 12, "probe-owner-7", 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects stale and replayed SSH evidence handles")
val handle = ServerProtocolProbeHandle(
    generation: 7, sequence: 11, authority: "probe-owner-7",
    authenticated: true, channel_opened: true, sftp_subsystem_opened: true
)
expect(server_protocol_probe_handle_admitted(handle, 7, 11, "probe-owner-7", 0)).to_equal(true)
expect(server_protocol_probe_handle_admitted(handle, 8, 11, "probe-owner-7", 0)).to_equal(false)
expect(server_protocol_probe_handle_admitted(handle, 7, 11, "probe-owner-7", 11)).to_equal(false)
expect(server_protocol_probe_handle_admitted(handle, 7, 12, "probe-owner-7", 0)).to_equal(false)
```

</details>

#### rejects unauthenticated or channel-less SSH evidence

- rejects unauthenticated or channel-less SSH evidence
   - Expected: server_protocol_probe_handle_admitted(unauthenticated, 7, 12, "probe-owner-7", 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unauthenticated or channel-less SSH evidence")
val unauthenticated = ServerProtocolProbeHandle(
    generation: 7, sequence: 12, authority: "probe-owner-7",
    authenticated: false, channel_opened: true, sftp_subsystem_opened: true
)
expect(server_protocol_probe_handle_admitted(unauthenticated, 7, 12, "probe-owner-7", 0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS production server capability projection.
- SimpleOS production server capability projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3017d620d0565d06a5b84fc21247026a2e04522cf3e4f8f6ccb1b8f13ab3d3e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3017d620d0565d06a5b84fc21247026a2e04522cf3e4f8f6ccb1b8f13ab3d3e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3017d620d0565d06a5b84fc21247026a2e04522cf3e4f8f6ccb1b8f13ab3d3e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports only reachable HTTP/1.1 and HTTP/2 ALPN implementations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for HTTP/3 QUIC WebTransport WebSocket ALPN and unknown protocols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_server_protocol_capabilities_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds HTTP manifests to the production probe and evidence identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
