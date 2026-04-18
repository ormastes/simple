# LLM Approval Flow

**Status:** landed in `spm-winfs-llm-suite` (2026-04-18).

This guide walks a single "banking LLM asks to open a window" request end-to-end. Same flow applies to any sensitive LLM-initiated GUI or action.

## Actors

- **LLM service** — the model (Claude/Codex/Gemini) or an MCP tool acting on its behalf.
- **MCP dispatcher** — `src/lib/nogc_sync_mut/mcp/dispatch.spl`. Tools opt-in via `DispatchRegistry.register`.
- **SPM (Simple Process Manager)** — `src/app/simple_process_manager/…`. Owns privilege, approval, gate.
- **SWM (Simple Window Manager)** — `src/os/compositor/*`. Draws. Never authorizes.
- **User** — presented with a signed approval dialog.

## Happy-path sequence

```
1. LLM calls MCP tool, e.g. wiki_keyword or a hypothetical `request_window`.
2. Dispatcher wraps the call:
     a. privilege_service.check(principal, required_id_path)
     b. → missing? ApprovalRequest sent to SPM approval_broker
3. approval_broker renders a trusted surface:
     - SimpleOS: SWM reserves z-band; only SPM can composite into it
     - Host:     OS-native secure prompt (polkit/UAC/TouchID) preferred;
                 fallback is peercred-bound dialog with SPM-signed payload
4. User approves → SPM mints AuthorityToken {id_path, level, scope=OneShot}
5. approval_broker returns SignedAction { hmac = sign(token) }
6. Tool handler runs; output flows back through llm_gate_service.release:
     - output_gate.scan_and_gate (secret/PII scan)
     - content_authority.release_gate (level vs reader clearance)
     - on Hold → notify_user → audit_log + WM notification
7. Released bytes reach the caller.
```

## Spoofing resistance

- `approval_broker.verify_response(signed)` rejects any `SignedAction` whose HMAC does not match SPM's session key.
- On host, the session key is bound to the SPM daemon process via peercred (UNIX sockets) or named-pipe SID (Windows).
- SWM never signs approvals. A malicious app that draws a lookalike dialog cannot produce a valid `SignedAction`.

## Integration points

| Component | File | Hook |
|-----------|------|------|
| LLM dashboard HTTP emit | `src/app/web_dashboard/server.spl` | Body passes through `filter_response_body`. |
| LLM dashboard main | `src/app/llm_dashboard/main.spl` | `gate_llm_emit(body, token)` helper. |
| MCP wiki tool | `src/app/mcp/wiki_keyword/wiki_tool.spl` | Returns `Content{body, authority}`. |
| MCP dispatcher | `src/lib/nogc_sync_mut/mcp/dispatch.spl` | `dispatch_wrap` runs privilege check + gate. |
| WM create/destroy | `src/os/compositor/hosted_backend.spl` | Calls `notify_window_created/destroyed`. |
| WM ↔ web bridge | `src/app/ui.web/wm_bridge.spl` | `resolveWinFsPath(app, wid) → text`. |

## Cross-reference

- `../04_architecture/simple_process_manager.md` — service layout.
- `../04_architecture/privilege_id_system.md` — IdPath model.
- `../04_architecture/win_fs_schema.md` — `/win` tree.
