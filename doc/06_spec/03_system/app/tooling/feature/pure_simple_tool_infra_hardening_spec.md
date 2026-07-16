# Pure-Simple Tool and Infrastructure Hardening

Source: `test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl`

Status: Implemented, production qualification blocked by deployed seed runtime

## Purpose

This qualification prevents a production-looking launcher, green test summary,
or cached tool artifact from hiding a seed/debug runtime, partial execution,
unsafe shell boundary, or stale result.

## Admit a pure-Simple production runtime

The runtime candidate is identified by behavior and provenance, not its path.
A Rust bootstrap seed or debug binary is rejected before the requested command.
Deployment validates a seed-free candidate in the destination layout before
the atomic swap, retains a runnable rollback candidate through post-swap
probes, and removes the construction seed only after admission succeeds.

## Run truth-preserving developer tools

Test child failure is authoritative. Parsed summaries can explain a failure but
cannot erase it. Multiple sibling test groups must all execute, nested daemon
runs bypass the owning serial daemon, and CLI outcomes distinguish assertion,
usage, internal, empty-discovery, and timeout/resource failures.
The interpreter wrapper compares authored and reported example counts when no
filter is active. Checker global flags and the pure-Simple `gen-lean` worker are
deadline-bound; `gen-lean` never dispatches back into itself.
Batch children use the same bounded process facade and translate deadline
termination to exit 124. Daemon PID checks and startup use argv-safe process
operations, and request writes fail closed if their atomic rename fails.

Lint uses the compiler's scoped annotation parser. Lint, format, and fix share a
single behavior owner and production entrypoints do not execute raw source
workers. Repository-wide UI and hot-loop gates run only for explicit `--all`;
focused lint remains scoped. `check` truthfully promises parse/validation only
until full type inference has an enforcing implementation.

## Reject unsafe paths and stale fallbacks

Duplicate-check walks and reads files through Simple IO APIs. Paths containing
spaces, apostrophes, semicolons, wildcard characters, or shell operators remain
data and cannot execute a command. One canonical benchmark provides real
result, persistence, and cache assertions.

MCP and LSP launchers select validated cached native artifacts. A missing or
failed native probe is an explicit failure, never permission to run source,
debug, or seed fallbacks. Probe stamps are keyed by the validated SHA-256
identity, and production has no environment switch that bypasses probing.
Native smoke evidence reads only log records appended by its current invocation
and corrupts the selected candidate's exact stamp. It passes stale-stamp repair
only when the current re-probe succeeds and rewrites the expected content hash.
Windows routes all three launchers through one bounded SHA-256/protocol
admission helper and preserves argument forwarding.
Its contract uses isolated fake native executables to reject absent/mismatched
sidecars, correlated protocol errors, stale content-addressed stamps, and
missing explicit MCP/LSP overrides without touching production artifacts.

The production test-daemon probe exercises `clean`, cache hit, source-change
miss, status, and stop through the selected qualification binary. Cached and
executed paths preserve the same exit outcome, while the response records
`clean`, `hit`, or `miss`.
Main CLI dispatch reaches the daemon application's real owner, and dependency
cache keys use content hashes so same-size dependency rewrites invalidate.
CLI, test-runner client, launcher, and daemon child share one executable
selector. A valid `SIMPLE_BINARY` pre-deploy candidate wins and is spawned with
an argv vector, so qualification never silently switches to deployed tooling.

## Measure warm tooling budgets

After one discarded warm-up, focused CLI and single-test samples retain p95
latency. MCP/LSP evidence includes wrapper startup, correlated warm requests,
and max RSS. Runner evidence covers a representative 1,000-test workload with
batch-boundary reclamation. Cache cold, warm, and invalidated runs must agree on
outcomes.

The retained production commands are
`scripts/check/check-test-runner-rss-batch.shs` and
`scripts/check/check-mcp-lsp-nfr-evidence.shs`. Native server hashes must match
their adjacent bootstrap-generated `.sha256` sidecars before wrappers execute.

## Expected outcome classes

| Outcome | Exit |
|---|---:|
| pass | 0 |
| assertion failure | 1 |
| usage error | 2 |
| internal error | 3 |
| empty discovery | 4 |
| timeout/resource termination | 124 |

## Current qualification state

The source contracts are implemented. The executable spec remains red while
`bin/simple` identifies itself as the Rust bootstrap seed, so latency, RSS,
daemon, checker, MCP, and LSP production evidence cannot yet qualify the
pure-Simple route. A passing manual without those executable production probes
is not accepted as qualification evidence.
Windows source parity is implemented; executable Windows and pure-runtime
qualification remain required before PASS.
