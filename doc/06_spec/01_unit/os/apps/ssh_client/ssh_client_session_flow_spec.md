# Pure-Simple SSH Client — Full Socket-Free Session Flow

> Drives the complete client state machine end to end without a socket: banner exchange, KEXINIT, curve25519 key exchange with host-key pinning, NEWKEYS, service request, password userauth, session channel open, `exec`, output collection and exit status.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple SSH Client — Full Socket-Free Session Flow

Drives the complete client state machine end to end without a socket: banner exchange, KEXINIT, curve25519 key exchange with host-key pinning, NEWKEYS, service request, password userauth, session channel open, `exec`, output collection and exit status.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Drives the complete client state machine end to end without a socket: banner
exchange, KEXINIT, curve25519 key exchange with host-key pinning, NEWKEYS,
service request, password userauth, session channel open, `exec`, output
collection and exit status.

The peer is the real sshd code wherever a builder exists (`ssh_build_kexinit`,
`ssh_build_kex_ecdh_reply`, `ssh_build_newkeys`, `ssh_build_service_accept`,
`ssh_build_auth_success`) plus the real curve25519/ed25519 primitives, so this
is a genuine in-process client<->server run rather than a mock.

Covers:
  1. Every state transition in order, with the expected outbound payload.
  2. `exec` output and exit status reaching the caller.
  3. The same flow REFUSED at the key-exchange step when the host key is not
     pinned — the session never reaches userauth, so no password is ever sent
     to an unverified peer.

tag: unit, ssh, ssh_client, session, security

## Scenarios

### SSH client full session flow without a socket

#### runs banner through exec and collects output and exit status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs banner through exec and collects output and exit status
   - Expected: started.is_ok() is true
   - Expected: started.unwrap().has_outbound is true
   - Expected: started.unwrap().outbound.len() equals `23`
   - Expected: session.state equals `SSH_ST_BANNER`
   - Expected: after_banner.is_ok() is true
   - Expected: session.state equals `SSH_ST_KEXINIT`
   - Expected: session.server_banner equals `server_banner_text()`
   - Expected: after_banner.unwrap().outbound[0] equals `20`
   - Expected: after_kexinit.is_ok() is true
   - Expected: session.state equals `SSH_ST_KEXREPLY`
   - Expected: session.negotiated_kex equals `curve25519-sha256`
   - Expected: session.negotiated_host_key equals `ssh-ed25519`
   - Expected: ssh_parse_kex_ecdh_init(after_kexinit.unwrap().outbound).is_ok() is true
   - Expected: after_kex.is_ok() is true
   - Expected: session.state equals `SSH_ST_NEWKEYS`
   - Expected: session.session_id.len() equals `32`
   - Expected: session.keys.enc_key_c2s.len() equals `32`
   - Expected: after_kex.unwrap().outbound[0] equals `21`
   - Expected: after_newkeys.is_ok() is true
   - Expected: session.state equals `SSH_ST_SERVICE`
   - Expected: after_newkeys.unwrap().outbound[0] equals `5`
   - Expected: after_service.is_ok() is true
   - Expected: session.state equals `SSH_ST_AUTH`
   - Expected: after_service.unwrap().outbound[0] equals `50`
   - Expected: after_auth.is_ok() is true
   - Expected: session.state equals `SSH_ST_CHANNEL`
   - Expected: after_auth.unwrap().outbound[0] equals `90`
   - Expected: after_open.is_ok() is true
   - Expected: session.state equals `SSH_ST_EXEC`
   - Expected: session.remote_channel equals `5`
   - Expected: after_open.unwrap().outbound[0] equals `98`
   - Expected: after_exec.is_ok() is true
   - Expected: session.state equals `SSH_ST_RUNNING`
   - Expected: after_exec.unwrap().has_outbound is false
   - Expected: d1.is_ok() is true
   - Expected: d2.is_ok() is true
   - Expected: ssh_ascii_bytes_to_text(session.stdout_bytes) equals `SimpleOS x86_64`
   - Expected: st.is_ok() is true
   - Expected: session.got_exit_status is true
   - Expected: session.exit_status equals `0`
   - Expected: cl.is_ok() is true
   - Expected: session.state equals `SSH_ST_DONE`
   - Expected: cl.unwrap().outbound[0] equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("runs banner through exec and collects output and exit status")
var session = ssh_client_session_new(client_config(), known_hosts_pinned())

# The client speaks first.
val started = ssh_client_session_start(session)
expect(started.is_ok()).to_equal(true)
expect(started.unwrap().has_outbound).to_equal(true)
expect(started.unwrap().outbound.len()).to_equal(23)
session = started.unwrap().session
expect(session.state).to_equal(SSH_ST_BANNER)

# Server banner -> client KEXINIT.
val after_banner = ssh_client_session_step(session, banner_wire(server_banner_text()))
expect(after_banner.is_ok()).to_equal(true)
session = after_banner.unwrap().session
expect(session.state).to_equal(SSH_ST_KEXINIT)
expect(session.server_banner).to_equal(server_banner_text())
expect(after_banner.unwrap().outbound[0]).to_equal(20)

# Real sshd KEXINIT -> client KEX_ECDH_INIT, and sshd must parse it.
val after_kexinit = ssh_client_session_step(session, ssh_build_kexinit())
expect(after_kexinit.is_ok()).to_equal(true)
session = after_kexinit.unwrap().session
expect(session.state).to_equal(SSH_ST_KEXREPLY)
expect(session.negotiated_kex).to_equal("curve25519-sha256")
expect(session.negotiated_host_key).to_equal("ssh-ed25519")
expect(ssh_parse_kex_ecdh_init(after_kexinit.unwrap().outbound).is_ok()).to_equal(true)

# Real sshd KEX_ECDH_REPLY -> client NEWKEYS, with keys derived.
val after_kex = ssh_client_session_step(session, server_reply(host_blob()))
expect(after_kex.is_ok()).to_equal(true)
session = after_kex.unwrap().session
expect(session.state).to_equal(SSH_ST_NEWKEYS)
expect(session.session_id.len()).to_equal(32)
expect(session.keys.enc_key_c2s.len()).to_equal(32)
expect(after_kex.unwrap().outbound[0]).to_equal(21)

# NEWKEYS -> SERVICE_REQUEST ssh-userauth.
val after_newkeys = ssh_client_session_step(session, ssh_build_newkeys())
expect(after_newkeys.is_ok()).to_equal(true)
session = after_newkeys.unwrap().session
expect(session.state).to_equal(SSH_ST_SERVICE)
expect(after_newkeys.unwrap().outbound[0]).to_equal(5)

# SERVICE_ACCEPT -> USERAUTH_REQUEST (password).
val after_service = ssh_client_session_step(session, ssh_build_service_accept("ssh-userauth"))
expect(after_service.is_ok()).to_equal(true)
session = after_service.unwrap().session
expect(session.state).to_equal(SSH_ST_AUTH)
expect(after_service.unwrap().outbound[0]).to_equal(50)
expect(ssh_ascii_bytes_to_text(after_service.unwrap().outbound)).to_contain("hunter2")

# USERAUTH_SUCCESS -> CHANNEL_OPEN session.
val after_auth = ssh_client_session_step(session, ssh_build_auth_success())
expect(after_auth.is_ok()).to_equal(true)
session = after_auth.unwrap().session
expect(session.state).to_equal(SSH_ST_CHANNEL)
expect(after_auth.unwrap().outbound[0]).to_equal(90)

# OPEN_CONFIRMATION -> exec request on the peer's channel id.
val after_open = ssh_client_session_step(session, channel_open_confirmation())
expect(after_open.is_ok()).to_equal(true)
session = after_open.unwrap().session
expect(session.state).to_equal(SSH_ST_EXEC)
expect(session.remote_channel).to_equal(5)
expect(after_open.unwrap().outbound[0]).to_equal(98)
expect(ssh_ascii_bytes_to_text(after_open.unwrap().outbound)).to_contain("uname -a")

# CHANNEL_SUCCESS -> running.
val after_exec = ssh_client_session_step(session, channel_success())
expect(after_exec.is_ok()).to_equal(true)
session = after_exec.unwrap().session
expect(session.state).to_equal(SSH_ST_RUNNING)
expect(after_exec.unwrap().has_outbound).to_equal(false)

# Output, exit status, close.
val d1 = ssh_client_session_step(session, channel_data("SimpleOS "))
expect(d1.is_ok()).to_equal(true)
session = d1.unwrap().session
val d2 = ssh_client_session_step(session, channel_data("x86_64"))
expect(d2.is_ok()).to_equal(true)
session = d2.unwrap().session
expect(ssh_ascii_bytes_to_text(session.stdout_bytes)).to_equal("SimpleOS x86_64")

val st = ssh_client_session_step(session, channel_exit_status(0))
expect(st.is_ok()).to_equal(true)
session = st.unwrap().session
expect(session.got_exit_status).to_equal(true)
expect(session.exit_status).to_equal(0)

val cl = ssh_client_session_step(session, channel_close())
expect(cl.is_ok()).to_equal(true)
session = cl.unwrap().session
expect(session.state).to_equal(SSH_ST_DONE)
expect(cl.unwrap().outbound[0]).to_equal(97)
```

</details>

#### REFUSES a man-in-the-middle at key exchange and never sends the password

- REFUSES a man-in-the-middle at key exchange and never sends the password
   - Expected: session.state equals `SSH_ST_KEXREPLY`
   - Expected: refused.is_ok() is false
   - Expected: session.state equals `SSH_ST_KEXREPLY`
   - Expected: session.session_id.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REFUSES a man-in-the-middle at key exchange and never sends the password")
var session = ssh_client_session_new(client_config(), known_hosts_pinned())
session = ssh_client_session_start(session).unwrap().session
session = ssh_client_session_step(session, banner_wire(server_banner_text())).unwrap().session
session = ssh_client_session_step(session, ssh_build_kexinit()).unwrap().session
expect(session.state).to_equal(SSH_ST_KEXREPLY)

# A different, perfectly valid ed25519 host key is presented.
val refused = ssh_client_session_step(session, server_reply(mitm_blob()))
expect(refused.is_ok()).to_equal(false)
expect(refused.unwrap_err()).to_contain("HOST KEY MISMATCH")
# The session never advanced past key exchange, so no secret left the client.
expect(session.state).to_equal(SSH_ST_KEXREPLY)
expect(session.session_id.len()).to_equal(0)
```

</details>

#### REFUSES an unknown host and stops before userauth

- REFUSES an unknown host and stops before userauth
   - Expected: refused.is_ok() is false
   - Expected: session.session_id.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REFUSES an unknown host and stops before userauth")
var session = ssh_client_session_new(client_config(), known_hosts_empty())
session = ssh_client_session_start(session).unwrap().session
session = ssh_client_session_step(session, banner_wire(server_banner_text())).unwrap().session
session = ssh_client_session_step(session, ssh_build_kexinit()).unwrap().session
val refused = ssh_client_session_step(session, server_reply(host_blob()))
expect(refused.is_ok()).to_equal(false)
expect(refused.unwrap_err()).to_contain("unknown host key")
expect(session.session_id.len()).to_equal(0)
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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51fcca73e47c1ab45c0505abdd92ed7a474f44849f77df17f1cb83fa65ed7c00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51fcca73e47c1ab45c0505abdd92ed7a474f44849f77df17f1cb83fa65ed7c00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51fcca73e47c1ab45c0505abdd92ed7a474f44849f77df17f1cb83fa65ed7c00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl
mirror: doc/06_spec/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl:204:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs banner through exec and collects output and exit status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl:302:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REFUSES a man-in-the-middle at key exchange and never sends the password' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/ssh_client/ssh_client_session_flow_spec.spl:319:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REFUSES an unknown host and stops before userauth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
