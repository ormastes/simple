# Server context local research

Source base: origin/release/1.0.0, inspected 2026-11-15.

- `src/lib/common/config_core/host_config.spl`: pure layered machine defaults.
- `src/lib/common/contracts/orchestration/host_config_v1.spl`: administrative
  controller/runtime/credential references, not transport or enrollment proof.
- `src/app/llm_caret/orchestrator_client.spl`: compiled local metadata client.
- `src/app/llm_caret/orchestrator_execution_client_v2.spl`: compiled local
  signed-dispatch client; output correlation must remain intact.
- `src/app/orchestrator/local_controller.spl`: submit/inspect/cancel with owned
  journal cleanup. There was no remote controller transport at research time.
- `src/lib/nogc_sync_mut/daemon_sdk/local_gateway_*_v1.spl`: bounded framing
  and local peer-authenticated transport. Framing is reusable; host-service
  commands are not equivalent to controller metadata operations.
- `src/app/build/scheduler/trusted_ssh.spl`: strict explicit OpenSSH option
  pattern. The serial SSH helper disables host-key checking and is unsuitable.
- `src/lib/nogc_sync_mut/io/process_ops.spl`: owned V3 process start accepts
  bounded stdin and exposes poll/collect/retained ownership.
- `src/lib/nogc_async_mut/container/api_v2.spl`: single backend owner API.
- `src/app/llm_caret/messaging/config.spl`: messaging listener remains local;
  orchestration client selection does not change its listener policy.

The inspected user host.sdn has no server endpoint and servers.sdn is absent.
No live address, credential profile, host key or installed remote executable
was discovered. Examples cannot be reported as live setup.
