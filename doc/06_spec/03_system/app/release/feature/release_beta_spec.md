# Release Beta Qualification

> Initial manual-first mirror. Regenerate with SPipe docgen from the executable spec after the fresh Stage 4 CLI is admitted.

Operators qualify one source revision through strict self-hosting, the exact fresh full CLI, every selected non-macOS package, and the repository's real GitHub release workflow. Missing or substituted evidence fails closed.

## Primary flow

1. Calibrate the fail-closed release receipt contract.
2. Build the strict bootstrap chain.
3. Qualify the fresh full CLI.
4. Validate release payloads and tool servers.
5. Audit the platform workflow matrix.
6. Record the releasable beta handoff.

## Expected evidence

- strict bootstrap and disabled stub fallback;
- exact Stage 4 identity plus test/lint/duplicate markers;
- checker contract receipts for executable, payload, SimpleOS, MCP, and LSP roles;
- validated Linux, FreeBSD, and Windows platform artifacts;
- production verification PASS;
- successful GitHub release workflow bound to the same revision and version.

## Failure behavior

Missing evidence directories, malformed receipts, revision or Stage 4 hash mismatches, blocked platform rows, source-only substitution for executable roles, and non-successful GitHub runs all fail closed with an actionable reason.

## Executable source

The folded executable source is `test/03_system/app/release/feature/release_beta_spec.spl`.
