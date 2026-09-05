# Simple Process Manager (SPM)

**Status:** landed in `spm-winfs-llm-suite` (2026-04-18).

## Purpose

SPM is the userland service that mediates between the kernel (SimpleOS) or host OS, the Simple Window Manager (SWM), the LLM dashboard, and MCP tools. It exists to make four capabilities possible without duplicating logic across platforms:

1. Hierarchical privilege IDs (`id.user.banking.view`) — single store, two lookup paths.
2. Windows-on-filesystem tree (`/win/<app>/<wid>/…`) — same `fs_encoder` on kernel mount and host shim.
3. LLM→GUI approval — one broker, one signing model.
4. LLM output release gate — one `llm_gate_service` behind the dashboard and MCP dispatcher.

SPM **does not** enforce security by itself on the kernel side. On SimpleOS, kernel enforcement happens in `src/os/kernel/ipc/capability.spl` via the `privilege_bridge` mirror; SPM is the userland authority that mints, revokes, and serves tokens over RPC. On the host, SPM is the sole authority — host OSes do not have our kernel.

## Layout

| Module | Role |
|--------|------|
| `src/app/simple_process_manager/main.spl` | Entry; picks transport via `SIMPLE_SPM_TRANSPORT`. |
| `src/app/simple_process_manager/spm_service.spl` | Core dispatch loop. |
| `src/app/simple_process_manager/privilege_service.spl` | Wraps `PrivilegeStore`; handles lookup/mint/revoke RPC. |
| `src/app/simple_process_manager/window_registry.spl` | Holds `[WindowRecord]`, publishes via `PublishSink`. |
| `src/app/simple_process_manager/approval_broker.spl` | HMAC-signed approval flow; verifies `SignedAction`. |
| `src/app/simple_process_manager/llm_gate_service.spl` | Composes `output_gate` + `content_authority` + `notify`. |
| `src/app/simple_process_manager/winfs_shim_host.spl` | Host-only publish sink; uses the same `fs_encoder`. |
| `src/app/simple_process_manager/transport/spm_transport.spl` | Trait. |
| `src/app/simple_process_manager/transport/spm_transport_simpleos.spl` | `sys_spm_send` / `sys_spm_listen`. |
| `src/app/simple_process_manager/transport/spm_transport_host.spl` | UNIX socket / named pipe. |
| `src/lib/common/spm/spm_rpc.spl` | Pure RPC schema (SDN wire). |

## Transport selection

```
SIMPLE_SPM_TRANSPORT=host     → SpmTransportHost (UNIX socket)
SIMPLE_SPM_TRANSPORT=simpleos → SpmTransportSimpleos / SpmTransportMock
(unset)                       → host default; compositor picks MockLoopback for smoke tests
```

## RPC surface (today)

- `PrivilegeCheck { principal, id_path } → bool`
- `WindowRegister { record } → u64`
- `WindowDestroy { wid } → ()`
- `ApprovalRequest { intent, principal } → SignedAction | Denied`
- `LlmReleaseCheck { content, content_authority, reader } → ReleaseDecision`
- `NotifyUser { reason, token } → ()`

All requests/responses travel as SDN bytes over the chosen transport.

## Why a separate service

The three alternatives were rejected:
1. **Kernel-only.** Would force host builds to reimplement enforcement from scratch, duplicating logic (the user's explicit rule).
2. **Library-only.** A library can't own a signing key or a trusted approval surface across processes.
3. **Per-app inline.** Would multiply the trusted surface; one service is auditable.

## Interaction with existing primitives

- Reuses `TrustLevel` from `src/app/package.registry/trust.spl`.
- Reuses `secret_scan`, `prompt_sanitizer`, `audit_log`, `credential_store`.
- Kernel stays MDSOC-only; SPM lives in userland MDSOC+ (ECS business layer).

## See also

- `privilege_id_system.md` — IdPath + AuthorityToken model.
- `win_fs_schema.md` — `/win/<app>/<wid>/…` path tree.
- `../07_guide/tooling/llm_approval_flow.md` — end-to-end walkthrough.
