# Caret provider CLI adapters V1 — selected scope

These requirements follow the explicitly requested Codex/Claude/Gemini/Kimi
adapter work and the user's Windows Docker/Linux Podman execution requirement.
They do not select a host-task fallback or expand authentication authority.

| ID | Required behavior | Current evidence |
|---|---|---|
| REQ-CARET-PROVIDER-001 | Recognize exact observed provider/version families; reject other versions and unknown providers | Production data decoder and unit specs authored; local help/version research observed |
| REQ-CARET-PROVIDER-002 | Construct correct per-provider Start/Resume argv and fixed machine output without shell task interpolation | Production planner and hostile-input specs authored |
| REQ-CARET-PROVIDER-003 | Protect prompt/model/session values and reject execution/protocol/auth/safety overrides in extras | Production allowlist and negative specs authored |
| REQ-CARET-PROVIDER-004 | Plan only actual read-only auth inspection or explicit external credential metadata; mutate no auth/billing state | Production planner/specs authored; no auth operations executed |
| REQ-CARET-PROVIDER-005 | Interrupt through the actual contained invocation/CoreMux control owner; retain charge until settlement | Neutral data intent authored; actual contained consumer still required |
| REQ-CARET-PROVIDER-006 | Capture container-installed version/help through genuine admitted Simple Container execution and complete bounded owned output | Common configuration/output producer coordinated with its owner; not yet implemented in this app slice |
| REQ-CARET-PROVIDER-007 | Bind compatibility to exact actual immutable image/program filesystem, runtime/provider/scope generation and fresh admission | Actual observation/selection consumer still required; caller image strings and local versions provide no grant |
| REQ-CARET-PROVIDER-008 | Route all new task effects through Windows Docker/Linux Podman common API; use CoreMux for interactive IO | Required architecture boundary; no new host task path or legacy-gate bypass authored |

Source/fixture qualification is **NOT_RUN**, with no coverage percentage or
native compatibility claim. Data tests do not satisfy the contained execution,
ownership, image binding or settlement requirements. Full feature completion
requires their actual producers/consumers and real system fixtures.
