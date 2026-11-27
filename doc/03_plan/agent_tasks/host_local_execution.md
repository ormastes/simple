# Finite local host execution composition

Status: approved design, implementation in progress. This is a local command subset, not a persistent daemon or remote endpoint. The preceding host replay slice is merged as PR 7551; its runtime qualification remains NOT_RUN.

## Owners and shared contracts

- Orchestrator owns canonical command routing and `HostExecuteRequestV1`: original reservation envelope, intent, prepared receipt, scoped launch plan, bounded canonical request bytes, signed grant and signed approval. It owns plan/common codecs and controller dispatch/inspect.
- Host Astra lead owns local policy/root admission, signed host turns, retained observations and exact writer close. Sole Sol worker implements `local_authority_policy_v1` and focused negative specifications; Astra reviews exact source and evidence.
- Daemon owner admits existing shared signature verification/snapshot mechanisms. Its explicit owner-returning polling API is a later persistent-service dependency, not a shortcut through mutable callback capture.
- Podman owner admits payload-bound requests and codec, then observes actual provider identity using the existing owned executable pin/process owner. Host must not duplicate Podman shell-outs or infer storage continuity from a healthy probe.
- Caret invokes the eventual compiled controller/host route. Smux remains the only terminal stream owner; terminal/device scope is refused in this first CPU-only path.
- Root coordinates scarce build slots, dependency order and landing. No heavy build without a slot.

## First external path

The proposed canonical compiled orchestrator commands are `host-prepare <protected-root> <request-file>`, `host-execute <protected-root> <request-file>` and `host-inspect <protected-root> <operation-id>`. Local administrator root initialization must precede them. Local init creates an owned private root, validates and publishes a public authority registry, observes actual native boot identity and actual pinned provider identity, then publishes the host binding. It never accepts request-supplied signing keys, clocks, provider epochs or continuity flags.

For execution, decode the canonical provider request and recompute its semantic digest; do not substitute a hash of serialized SDN. Match operation ID explicitly because the semantic digest deliberately excludes it. Verify both roles against the derived `host_execute_v1` envelope; the original `host_reservation_v1` remains the immutable prepared identity. Refresh trusted clock/policy/revocation/session state immediately before committing execution. The V2 journal commit precedes create/start. Retain bounded create/start observations and verify their bytes before writing stdout. Start observed is not completed. Publication failure preserves capacity and requires inspection, not relaunch.

Close releases only the exact journal writer. Reopen of executing work becomes outcome-unknown and reconciles the exact provider native ID. Provider failure is never evidence that nothing ran. Unknown or legacy unbound provider work remains charged. Legacy provider records may support exact inspect/stop/destroy, never new create/start authorization.

## Required evidence and current gaps

Real system acceptance submits an actual immutable request, independently inspects native container identity/state and nonce output, then reopens the host journal and verifies no second execution. Negative cases cover swapped command bytes, operation mismatch, wrong boot/provider identity, forged signatures, expired approval, capacity overflow, and lost response after execution commit. No constructor-only or scripted-provider result can satisfy the native gate.

Current blockers are explicit: no admitted runtime or live Podman fixture; shared signature/snapshot and provider request-binding source foundations are pending; protected root initialization, real provider continuity observation and durable host observations are not implemented. Existing HostConfig is administrative intent, not attestation. File modes and a stored generation alone do not prove native ownership or continuity. First init-only/non-adoption source behavior may be admitted as a narrower step, but cannot satisfy replay/recovery acceptance.

The maintenance scan latency audit is deferred and excluded. No full host completion claim is permitted until the actual submitted-work acceptance path passes.

Provider pin limit: the existing OwnedExecutablePin accepts static ELF images only (no PT_INTERP/PT_DYNAMIC, at most 64 MiB). A native `podman info` observation is not an immutable executable pin. Initial strict policy must refuse an unsupported pin requirement; there is no automatic fallback to ordinary PATH execution. A separately authorized trusted-host execution capability would be a distinct explicit policy, not an attestation claim. Dynamic-Podman owner support remains an acceptance gap.
