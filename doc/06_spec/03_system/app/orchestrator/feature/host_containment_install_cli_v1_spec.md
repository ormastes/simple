# Public containment installation routing

Status: **NOT_RUN**. Authored manual, not execution evidence.
Requirements: ORCH-02, HOST-02.
Spec: `test/03_system/app/orchestrator/feature/host_containment_install_cli_v1_spec.spl`.

The actual public dispatcher routes `host-containment-install <protected-root>
<signed-packet-file>` to the existing Host command owner. That owner verifies the
signed configuration through the same operation journal and reports
`installed: true`, `containmentReady: false` on successful installation.
Configuration does not enable capture, prove containment, or release capacity.

| Exact step | Checks |
|---|---|
| routes missing containment installation arguments to the actual host domain | Call the public dispatcher with only the action; require Host argument-count error, exit 1 and no cleanup owners. |
| refuses extra containment arguments before opening either caller path | Supply an extra argument and unused paths; require Host argument-count error, exit 1 and no cleanup owners. |

The scenarios require the real Host installer dependency. They do not mock
filesystem state or construct a native owner, and make no successful installation
or provider-readiness claim. The configured containment capture source is held
separately; this route does not bypass that gate.
