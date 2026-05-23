<!-- codex-design -->
# Security Convention-First Architecture

## Pattern

Use convention-first MDSOC coordinate inference as a compiler graph feature.

The coordinate resolver accepts two layouts:

- Legacy: `src/feature/<feature>/<layer>/...`
- Convention-first: `src/<layer>/<feature...>/...`

The convention-first layout is preferred for new code because it makes layer the top-level architecture dimension and feature the remaining folder path.

## Enforcement

The security checker builds a feature/layer edge graph from source fallback facts and HIR facts where available.

For same-feature edges:

- Adjacent layer descent is allowed.
- Skipping more than one default layer emits `SEC101`.

For cross-feature edges:

- Existing `SEC201` gate enforcement remains authoritative.
- Cross-feature port imports remain allowed as existing behavior.

## Default Layer Order

Default order:

`ui -> api -> service -> domain -> port -> infra -> driver -> kernel`

This is a built-in convention for this slice. Future source/SDN policy merge can make layer order configurable while preserving safe defaults.

## Fit With Existing Security AOP

This slice does not change AOP weaving. It strengthens the graph facts that feed architecture diagnostics. Gate weaving, policy checks, sandbox entry, and audit runtime calls continue to use the existing `SecurityAdvicePlan` path.
## 2026-05-23 Live KMS CI Hardening Architecture Addendum

The live KMS gate remains outside normal CI execution. The architecture is:

- GitHub Actions manual workflow dispatch selects a provider.
- A provider-specific protected environment gates access to credentials.
- A provider-specific preflight step fails if required credential environment variables are absent.
- The same Simple integration spec exercises the selected provider through `SIMPLE_LIVE_KMS_PROVIDER`.
- Repo hygiene calls a local structural checker that guards the workflow shape.

The local checker is intentionally shell-only with an optional `actionlint` branch. This avoids making basic repository hygiene dependent on downloading a third-party binary while still allowing stricter validation on developer machines or CI images that already provide `actionlint`.

OIDC is the preferred future credential-delivery pattern for cloud providers, but it should be introduced provider-by-provider because it changes environment permissions and provider setup. The current bearer/authorization variables remain the compatibility path for existing KMS gateway tests and the HSM lane.
