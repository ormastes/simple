<!-- codex-research -->
# LLM Caret + SPipe infrastructure access hardening NFRs

Selected: NFR option 2 (production-balanced evidence) on 2026-07-18.

- NFR-LCSI-001: Default tests must be deterministic and offline; no normal
  developer or CI run requires provider credentials, network access, or
  destructive external fixtures.
- NFR-LCSI-002: Every selected provider must have an opt-in read-only live smoke
  path. Write/destructive live tests must use disposable fixtures and a separate
  explicit enable flag or permission grant.
- NFR-LCSI-003: No token, password, mail body, attachment, object content, or
  other secret may appear in argv, logs, model-visible diagnostics, generated
  manuals, or retained test output unless explicitly requested and permitted.
- NFR-LCSI-004: Retries must be bounded, honor `Retry-After` or provider
  equivalents, and must not blindly replay non-idempotent writes.
- NFR-LCSI-005: Provider IDs, opaque cursors, error/request IDs, retry metadata,
  and raw escape-hatch output must survive normalization without semantic loss.
- NFR-LCSI-006: Large objects and attachments must use streaming-capable routes;
  the compatibility layer must not require whole-payload buffering.
- NFR-LCSI-007: Human output and stable JSON output are required; streaming or
  event operations must support NDJSON where applicable.
- NFR-LCSI-008: Warm local validation, permission, conversion, and dispatch
  planning must have p95 latency below 200 ms on the documented Linux
  qualification host, excluding external provider and child-process latency.
- NFR-LCSI-009: Input paths and downloaded filenames must remain confined to
  the configured workspace root and reject traversal.
- NFR-LCSI-010: Focused unit, integration, and SPipe coverage must exercise at
  least 80% of new compatibility-layer branches, including happy, edge, and
  error paths for every requirement.
- NFR-LCSI-011: New production files must remain below 800 lines, introduce no
  local direct `rt_*` environment/process bypass, and add no silent stubs,
  placeholder passes, or hardcoded success results.
- NFR-LCSI-012: Live evidence must identify the actual adapter, transport,
  provider, safety class, result status, elapsed time, and whether a destructive
  grant was required; fallback evidence cannot be attributed to another route.
