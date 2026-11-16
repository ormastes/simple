# Windows primary geometry V2 requirements

Selected scope: explicit user/parent request for actual Windows Docker primary-container geometry through the common Container API and the existing generic V5 service. Source-only landing is authorized; native qualification remains pending.

- REQ-WINDOWS-PRIMARY-GEOMETRY-001: resize the exact running adopted TTY container using Docker API 1.48, with retained provider identity and native endpoint checks.
- REQ-WINDOWS-PRIMARY-GEOMETRY-002: enforce a separate Geometry lease, current adoption/issuer/revision and native write deadline; Input authority is independent.
- REQ-WINDOWS-PRIMARY-GEOMETRY-ATTEMPT-001: persist immutable attempts before effects, preserve Unknown across retries/rotation/restart, and retain cleanup/publication owners.
- REQ-WINDOWS-PRIMARY-GEOMETRY-003: consume the common owner in generic V5 dispatch and periodic progress; report acknowledgement separately from observed size.
- REQ-WINDOWS-PRIMARY-GEOMETRY-NFR-001: bounded same-thread turns, one attempt-history pair per turn, no helper process, no blocking CLI probe, no second writer or terminal reader.

Benefits: required control capability with exact authority and recoverable evidence. Costs: bounded history storage and conservative manual recovery for ambiguous outcomes. Effort: provider, Host and V5 source integration plus a future admitted Windows native campaign. No alternative requirements remain unselected.
