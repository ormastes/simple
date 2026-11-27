# Proof-only retirement verification

Status: NOT_RUN, source-only additions to
`test/01_unit/lib/io/piped_process_owned_v2_spec.spl`.

- Tampered owner and mismatched reference reject before native retirement.
- Canonical preparation in a real private temporary directory installs matching
  immutable claim/request metadata only. Missing cleanup proof returns Err and
  leaves broker.control.request absent.
- Malformed broker.stream.unlaunched.sdn also refuses without a control action.
  Claim/request bytes and retained owner identity remain exact.
- No fixture writes a positive terminal/tree/unlaunched receipt or claims a
  broker/cgroup execution. Positive lifecycle qualification remains separate.

No tests/builds are allocated or run. Existing cleanup retains cancel+reread;
new retire performs one proof read and never cancels. Host settlement's two-line
import/call adaptation changes no journal/ACK schema. See the design artifact
`doc/05_design/process_retire_piped_owned_v2.md`.
