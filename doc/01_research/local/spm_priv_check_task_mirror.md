# SPM Privilege Check Task Mirror Local Research

Feature: FR-SPM-0002.

## Findings

- `privilege_bridge.spl` already stores mirrors keyed by task id and exposes
  `bridge_lookup` plus `two_gate_check`.
- `syscall_handler` already resolves the current caller task for capability
  checks before dispatching syscall 110.
- `_handle_spm_priv_check` copied the id-path bytes but always returned deny.

## Decision

Route syscall 110 through the already resolved caller task id and evaluate the
copied id path with `bridge_lookup(caller_task_id)` and `two_gate_check`.
