# Output-only runtime transport adoption

Status: source integration in progress; awaiting verification. This is not a
complete runtime-bind service or interactive terminal implementation.

The current exclusive local composition is specified in
[smux_exclusive_runtime_binding_v3.md](smux_exclusive_runtime_binding_v3.md).
The unsupported POSIX lifecycle statements below describe the original
unowned reference API; the newer complete group-owner bundle has a distinct
cleanup/settlement path. Neither source implementation is runtime-qualified.

REQ-SMUX-RUNTIME-BOUNDARY-001: server authentication precedes capability and
bind dispatch. The negotiated text protocol must not be exposed through the
unauthenticated local remote-command dispatcher or described as a complete
framed CoreMux server.

REQ-SMUX-RUNTIME-BOUNDARY-002: when no host-resolved runtime binding owner is
installed, capability discovery and binding refusal report explicit absence,
with no journal commitment, stream ownership, pane or configuration mutation.

REQ-SMUX-RUNTIME-REF-001: retain the canonical PipedProcessRefV1 across every
PaneRecord clone, service publication and split checkpoint. A different
registry generation is a different execution reference even if its numeric
PID is reused, and must invalidate child-incarnation capture state.

REQ-SMUX-RUNTIME-REF-002: canonical transports use only generation-checked
SOSIX operations. No liveness, read, close or cleanup fallback may use the PID
alone. Smux's existing pane poller is the sole reader. Exited is not drained:
Ok(None) means deferred, and only process_stdout_eof proves observed drained
EOF. Other errors remain explicit and must not trigger a busy retry loop or
fabricated stream completion.

REQ-SMUX-RUNTIME-REF-003: typed adoption validates service epoch/revision,
target identity/incarnation, vacancy and a real canonical owner before the
single API publication. Failed adoption leaves reference cleanup with its
caller. No bind request supplies a raw PID/reference or a command to execute.
Adoption means helper ownership/opening, not completed Podman attachment.
Side-effect-free exact-reference validation admits an existing registry owner;
it does not require or establish process liveness. POSIX liveness returns
`process_liveness_unsupported` without waiting or reaping. EOF is stream state,
not proof of process exit.

REQ-SMUX-RUNTIME-REF-004: this transport is output-only. Input, paste, command
delivery, generated VT replies and native geometry changes must not reach the
transport. Legacy PTY and piped behavior remains with its existing owners.
Provider-owned attach fixes --no-stdin and --sig-proxy=false; closing its helper
must never be reported as workload cancellation, termination or removal.

REQ-SMUX-RUNTIME-REF-005: failed canonical close retains the owner state for
explicit cleanup; rollback and reset cannot silently discard it. Snapshot
generation, reference generation and service epoch are distinct identities.
The reference is valid only within its issuing process registry lifetime;
persisted/remote records cannot recreate it after a restart.
On the current POSIX backend, canonical close returns
`process_close_unsupported` without signals or slot release. Smux must retain
the exact owner and refuse pane/window/session removal. This is an unfinished
cleanup capability, not successful detach or termination. Retained slots count
against the registry's 16-slot bound.

The shared daemon lane owns these exact SOSIX APIs:

- PipedProcessRefV1 with pid and generation;
- sosix_process_spawn_piped_ref_v1(cmd, args);
- sosix_process_validate_piped_ref_v1;
- sosix_process_read_stdout_ref_v1;
- sosix_process_write_stdin_some_ref_v1 (not used by this output-only consumer);
- sosix_process_is_piped_alive_ref_v1;
- sosix_process_close_piped_ref_v1.

The provider opens the canonical reference through the corresponding shared
spawn API using an approved absolute executable. The actual runtime bind
service still requires host-retained execution resolution, provider session
capability, exact target-bound immutable request, journal begin/settlement,
replay and a consumed Caret binding/status path. It must not be synthesized
from caller-supplied observation or an attach argv plan.

Verification is split explicitly: current production-route refusal specs and
pure reference-state regressions check their own implemented boundaries.
Native stream EOF/drain/close and end-to-end Podman/smux behavior require real
providers and an admitted producer. Synthetic reference values in pure tests
are never passed to native operations or counted as stream evidence.

No build is authorized for this lane yet. The campaign-wide limit is five
CPU cores total; root owns build allocation. Runtime tests, docgen and full
system acceptance are NOT_RUN, not PASS.

## Authored verification mapping

| Requirement | Executable coverage |
|---|---|
| BOUNDARY-001/002 | `smux_runtime_binding_capabilities_spec.spl`: real authenticated dispatcher, exact absence/refusal, unchanged state and frame limits |
| REF-001 | `runtime_terminal_ref_spec.spl`: clone, generation/incarnation, revision and rollback identity |
| REF-002/003 | `smux_runtime_terminal_transport_spec.spl`: exact registry owner validation, real helper adoption, sole-reader fresh marker capture and explicit EOF |
| REF-004 | Both reference specs: pre-effect input refusal and changed-geometry rejection through the real resize path |
| REF-005 | Native-consumer scenario: unsupported POSIX close retains exact owner and prevents removal; liveness/exit remain explicitly unsupported |

The short requirement names in this table retain the `REQ-SMUX-RUNTIME-`
prefix above. All three specs are AUTHORED_UNRUN. Native dependency source,
producer admission, docgen and execution evidence remain outstanding;
POSIX process liveness/exit, successful teardown, restart recovery and full host/provider binding
are not qualified by the authored scenarios.
