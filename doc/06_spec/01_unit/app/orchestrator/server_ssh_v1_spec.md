# SSH profile, fixed command and response framing

Source: [server_ssh_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/server_ssh_v1_spec.spl).
Manually authored companion; **NOT_RUN**. No docgen, SSH process, credential-file
access or network exchange was executed for this specification.

## Manual flow represented by the assertions

1. Decode the strict reference-only SSH profile. Check the authentication and
   trust references, identity path and host-key alias. Legacy profiles retain
   empty optional `sshDigest` and `storeRoot`; the extended profile carries a
   lowercase executable digest and a protected-store root.
2. Validate safe absolute POSIX or forward-slash drive paths. Construct argv
   only when profile references exactly match the selected server record.
3. Inspect argv for explicit identity and known-hosts paths, strict host-key
   checking, disabled agent/X11 forwarding, cleared forwarding rules, disabled
   implicit configuration and one fixed `gateway-stdio-v1` command. The authored
   assertions preserve stdin for the framed request.
4. Encode and decode a response containing Unicode and NUL bytes. Preserve the
   exact payload, request ID and nonzero domain exit code; validate the whole
   frame rather than accepting a prefix.

| Failure group | Authored rejection checks |
|---|---|
| Profile schema | Wrong kind/version/type, unknown inline-secret field, raw auth value, missing/duplicate fields, trailing document and oversized input. |
| Executable identity and paths | Uppercase or nontext digest; relative, traversal, empty-segment, UNC, ADS and shell-bearing paths. |
| Command authority | Auth/trust mismatch; option injection through user, alias, identity path, host or remote executable; non-SSH record. |
| Response integrity | Wrong request ID, trailing/truncated/malformed bytes, byte-count mismatch, remote handle metadata and request frame presented as a response. |

Requirements: REQ-002/003/004 and NFR-001/002/003 at the profile/codec boundary.
The source assertions do not exercise private file admission, process launch,
Windows handle lifecycle, timeout/collection, a real host-key handshake or
remote mutation. See the [verification plan](../../../../03_plan/sys_test/server_contexts.md)
and [setup guide](../../../../07_guide/tooling/orchestration_server_contexts.md)
for those pending gates. Platform-dependent file/process work remains with
the generic counted-stdin facade and retained store owners.
