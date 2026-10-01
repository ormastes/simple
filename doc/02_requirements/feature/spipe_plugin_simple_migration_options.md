# Requirement Options: SPipe Plugin Simple-Language Migration

Feature: migrate the SPipe plugin's executable surfaces (CLI, MCP server)
from Node.js to the Simple language, with tests, Windows+POSIX parity, a PR
to Spipe main, and a host submodule pointer bump.

## Option A — Full migration in one change (CLI + MCP, Node deleted)

Port all ~48 CLI subcommands and the MCP server to `.spl`; delete
`cli/spipe.js` / `mcp/server.js`; update package.json bin, plugin metadata,
build.sh.

- Pros: single clean end state; no dual-maintenance; smallest final package.
- Cons: highest risk — the fine-tune family is ~1200 of 1637 CLI lines and
  the symlink/chmod stdlib gap blocks exact parity; one giant PR is hard to
  review; any port bug breaks every SPipe consumer at once.
- Effort: High (est. 3-5 engineering days + review + Windows validation).

## Option B — MCP server only; CLI stays Node

Port `mcp/server.js` (187 lines, SDK-supported) to
`mcp/server_main.spl`; re-point `plugin.json`/`manifest.sdn`; leave the CLI
on Node.

- Pros: smallest blast radius; MCP is the surface AI agents actually load;
  proves the runtime/wrapper/packaging path end-to-end.
- Cons: leaves the Node dependency in the package; CLI still requires Node
  on Windows hosts; only half the stated goal.
- Effort: Low-Medium (est. 1 day).

## Option C — Staged strangler: MCP + core CLI first, fine-tune family second (RECOMMENDED)

Stage 1 (this PR): `.spl` MCP server + core CLI commands
(info/experts/link-plan/doc-root/doctor/skill/guides + doc-link via shell
delegation), Node files kept as fallback for unported fine-tune commands;
`spipe`/`spipe-mcp` sh + `.cmd` wrappers choose the native `.spl` build when
available; golden-output parity tests (Node vs Simple) in CI; build.sh runs
both harnesses.
Stage 2 (follow-up PR): port the `fine-tune-*` family command-by-command
with the same parity harness, then delete the Node CLI.

- Pros: reviewable increments; parity is mechanically verified, not assumed;
  Windows/POSIX wrapper strategy proven on the small surface first; stdlib
  gaps (symlink/chmod) are discovered on low-stakes commands; matches
  strangler-fig prior art (see domain research).
- Cons: temporary dual implementation; dispatch/fallback logic adds a little
  wrapper complexity; two PR cycles.
- Effort: Medium (est. 2-3 days for stage 1; similar for stage 2).

## Option D — Metadata-only plugin update

Keep all Node code; only update plugin metadata/docs to describe SPipe.

- Pros: trivial.
- Cons: does not perform the migration; contradicts the host repo's
  pure-Simple toolchain rule (AGENTS.md: default tooling is the self-hosted
  binary, not Node).
- Effort: Trivial.

## NFR options

### NFR-A1 Startup + footprint parity
Targets: MCP `initialize` reply < 1.0 s warm on POSIX and Windows
(source/interpreter mode acceptable; native preferred); max RSS < 100 MB
(matches `SIMPLE_MEMORY_LIMIT_MB=100` convention in bin wrappers).
Verification: scripted handshake timing in build.sh + host
`scripts/check/check-mcp-native-smoke.shs`-style probe.

### NFR-A2 Windows/POSIX parity
Targets: every ported subcommand produces byte-identical stdout/exit codes
on macOS/Linux and Windows (modulo path separators); `.cmd` wrapper mirrors
`bin/simple_mcp_server.cmd` admission rules (sha256 sidecar for native exe,
per-process stderr dirs).
Verification: parity harness run on both platforms in CI; junction-vs-symlink
behavior of setup scripts unchanged and covered by existing gitlink checks.

### NFR-A3 Test coverage
Targets: 100% of ported subcommands have at least one golden-output test;
fine-tune lifecycle (stage 2) keeps the build.sh end-to-end exercise green;
new BDD specs land in the SPipe repo `test/` (run by host runtime) with
host-side mirrors under `test/03_system/app/spipe/feature/`.
Verification: `bin/simple test` runs + `sh scripts/build.sh` = pass.

### NFR-A4 Zero Node dependency (end state)
Targets: after stage 2, `node` is not required for any SPipe surface;
package.json bin points at sh/cmd launchers (or a documented runtime
requirement); `node --check` removed from build.sh.
Verification: build.sh passes in a PATH without node.

(Recommendation: select Option C with NFR-A1..A4; A4 binds stage 2.)
