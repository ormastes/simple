# Selected server configuration requirements

The user's explicit shared/per-service server request selects this scope.

- REQ-001: Simple, Orchestrator, Caret and agent consumers select shared or
  independent named SDN servers and contexts with deterministic overrides.
- REQ-002: Validate addresses, references, limits and transport requirements;
  reject invalid explicit configuration without silent local fallback.
- REQ-003: Preserve existing local commands when no server configuration is
  selected. Remote controller commands use typed authenticated SSH requests.
- REQ-004: Remote submit/status/cancel retain controller journal and identity
  semantics; dispatch retains signed host authorization and owner cleanup.
- REQ-005: Container discovery uses explicit reachable endpoints through the
  Simple Container backend boundary, without exposing runtime sockets.
- REQ-006: Document actual setup, credential references, unsupported modes,
  retained uncertainty and unexecuted qualification in the LLM wiki and skills.
- REQ-007: Generate a shared host SSH identity from OS cryptographic entropy;
  user text or current time selects the label only. Never transmit private keys.
- REQ-008: Send public registration requests over authenticated SSH and pin a
  verified received server key without replacing an existing identity or alias.
  Pending registration is not authorization; SSH proves login-key possession.
- REQ-009: Retain private store ownership, atomically publish with no replacement,
  enforce POSIX permissions/Windows ACLs, and track stronger protected storage.

Live deployment additionally needs the user's actual server address, SSH
account, credential/host-key references and installed remote executable.

Current implementation boundary: the application can prepare unsigned container
requests with selected public discovery before hashing. The application
composition that obtains reservations, signs, submits and dispatches those
requests remains open. Windows SSH also remains blocked on a safe external
private-file path projection. Neither boundary is marked complete by source
review or by the presence of lower provider APIs.
