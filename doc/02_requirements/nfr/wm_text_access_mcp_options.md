<!-- codex-research -->
# WM Text Access MCP — NFR Options

Date: 2026-06-01

## Option 1: Conservative Local/TRACE32 Targets

**Description:** Scope NFRs to TRACE32 and in-process Simple UI adapters only.

**Pros:**
- Easy to verify in existing tests.
- Avoids platform accessibility permissions.
- Lowest performance risk.

**Cons:**
- Does not prove arbitrary host-window behavior.
- Leaves OS accessibility adapter targets undefined.

**Effort:** S.

Targets:
- Snapshot/query/action p95 under 20 ms for in-memory adapters.
- TRACE32 command/capture operations timeout-bounded and reported with source/capability metadata.
- No repeated full-tree scans in hot handlers.

## Option 2: Adapter Contract Production Gate

**Description:** Define production targets for the shared adapter envelope and require each adapter to publish capabilities, confidence, staleness, and invalidation behavior.

**Pros:**
- Fits TRACE32, Simple UI, WM fallback, and future OS accessibility adapters.
- Prevents callers from treating screenshot or WM-only data as semantic control data.
- Gives verify concrete release gates.

**Cons:**
- More design/test work than TRACE32-only.
- Some targets are adapter-class-specific rather than universal.

**Effort:** M.

Targets:
- In-memory snapshot/query/action p95 under 20 ms on representative fixtures.
- Shell/remote adapters must cache where safe and expose max age/staleness.
- Hot MCP handlers must not shell out repeatedly without explicit adapter cache/invalidation design.
- Adapter status must report unsupported operations instead of silently falling back.
- MCP responses must include source and capability metadata.

## Option 3: Cross-Platform Accessibility Production Gate

**Description:** Require UIA/AX/AT-SPI adapters to meet latency, memory, permission, and reliability targets before the feature is accepted.

**Pros:**
- Strongest guarantee for arbitrary host applications.
- Forces realistic platform verification early.

**Cons:**
- High CI/environment complexity.
- Permission prompts and desktop session availability make automation brittle.
- Wayland limitations may make some targets impossible on some hosts.

**Effort:** L-XL.

Targets:
- Warm adapter startup under 500 ms per platform after permissions are granted.
- Representative accessibility-tree query p95 under 100 ms with cache enabled.
- Max RSS delta documented per adapter.
- Platform skips must be explicit and reported, not silent.

## Recommendation

Option 2 is the best NFR baseline. It makes the shared protocol production-grade while leaving OS accessibility adapters as explicit follow-on work with their own platform gates.

