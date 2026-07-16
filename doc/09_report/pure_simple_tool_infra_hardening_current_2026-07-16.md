# Pure-Simple tool and infrastructure hardening status

Date: 2026-07-16

## Executive status

Overall: **FAIL / source implementation substantially complete, production not
yet qualified**.

The selected C + 3 source fixes now cover atomic admission/rollback, truthful
runner outcomes, authored/executed guards, nested-daemon routing,
dependency-aware daemon caching, duplicate-check shell removal, canonical lint
ownership, measured duplicate benchmarking, `gen-lean` recursion removal, and
Unix native-first MCP/LSP wrappers. The final audit also closed main-dispatch
`gen-lean` recursion, unbounded batch workers, racy daemon-write fallback,
seed-dependent deployment admission, and weak wrapper probe-cache identity.
The post-sync audit additionally closed stale-daemon false hits, omitted batch
manifest entries, non-admitted rollback retention, and Windows native parity.
The deployed `bin/simple` still identifies itself as the Rust bootstrap seed,
so runtime and performance results from it cannot qualify pure-Simple
production behavior.

## Tool matrix

| Surface | Status | Bug / missing evidence | Root solution | Priority |
|---|---|---|---|---|
| Production runtime | BLOCKED | Clean Stage 2/3 now pass; full CLI Stage 4 still lacks a verified post-fix run | Re-run the bounded full bootstrap in a fresh session, admit, then atomically deploy | P0 |
| Test runner | IMPLEMENTED | Failure/outcome/count/nesting, exact manifest correspondence, and deadline-bounded batch re-exec implemented | Run 1,000-example RSS evidence on pure runtime | P0 |
| Duplicate checker | IMPLEMENTED | Runtime qualification blocked by seed | Run hostile-path and measured benchmark probes on pure runtime | P0 |
| Lint | IMPLEMENTED | Runtime qualification blocked by seed | Run canonical multi-name/scope fixture on pure runtime | P1 |
| Format/fix | WARN | Duplicate handlers and raw-source worker execution | One implementation; in-process or cached worker | P1 |
| Check | BLOCKED | Deployed artifact lacks required CLI extern; global flag timeout open | Repair/deploy shared CLI ABI; deadline-bound production probe | P1 |
| CLI dispatch | IMPLEMENTED | Statistics are table-derived; runtime evidence blocked by seed | Execute inventory probe after admission | P1 |
| Test daemon | IMPLEMENTED | Direct argv-safe startup/liveness, atomic fail-closed writes, and stale-sentinel handling implemented | Execute run/clean/hit/miss/invalidation matrix after admission | P2 |
| SPipe/docgen | WARN | Executable spec/manual exist; generated-doc validation blocked by seed | Regenerate once with admitted runtime | P1 |
| MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P1 |
| LSP MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P0 |
| Windows CLI/MCP/LSP | IMPLEMENTED | Shared bounded SHA-256 and real-protocol admission; executable Windows evidence missing | Run `check-windows-tool-wrapper-contract.ps1` on Windows | P0 |
| `gen-lean` | IMPLEMENTED | Main dispatch reaches the distinct deadline-bound worker; runtime proof blocked by seed | Run bounded invalid-subcommand/worker probe | P2 |

## Ranked work items

1. **PSH-001 — Provenance-safe atomic deploy:** admission check, rollback, and
   `--version`/`-c`/source-check post-swap evidence.
2. **PSH-002 — Duplicate-check security:** remove every shell-built discovery or
   file-read command; add hostile-path regression fixtures.
3. **PSH-003 — Runner truthfulness:** red, empty, two-sibling, internal-error,
   timeout, nonzero-child, and authored/executed-count contracts; stable outcome
   classes and nested no-daemon routing.
4. **PSH-004 — Lint correctness:** canonical annotation parser and handler.
5. **PSH-005 — Handler consolidation:** remove duplicate lint/fmt/fix paths and
   raw-source production execution.
6. **PSH-006 — Qualification evidence:** replace duplicate placeholder perf
   specs with one measured duplicate-check spec.
7. **PSH-007 — Native wrapper routing:** align MCP default and make LSP native
   probe/fail-closed; route installer through wrapper.
8. **PSH-008 — Windows parity:** remove Rust precedence after coordinating the
   currently dirty launcher lane.
9. **PSH-009 — Remaining tool defects:** checker deadline, test-runner RSS,
   nested timeout, test-daemon invalidation, and `gen-lean` recursion.

## Acceptance evidence required before PASS

- Runtime identity proves a non-seed pure-Simple deployment.
- Each production command has pass, usage-error, and internal-error evidence;
  test additionally has red and empty-discovery evidence.
- No placeholder assertions exist in retained qualification specs.
- Duplicate checker hostile paths cannot create a sentinel file.
- Warm latency/RSS targets match the selected NFR option.
- Linux and Windows wrappers select the same validated artifact class.
- Requirements, executable SPipe spec, generated manual, and implementation are
  traceable by ID.

## Current blockers

1. A clean admitted full-CLI runtime is unavailable. Isolated Stage 2/3
   self-hosting passed after adding the missing `copy_mem` runtime ABI alias.
   Stage 4 then exposed a `Dict`/`Map.keys` dispatch crash in async desugaring;
   the existing `rt_dict_keys` regression contract is restored, but the
   mandatory three-cycle cap prevents another full rebuild in this session.
2. NFR-007 and NFR-009 evidence harnesses exist, but their production latency
   and RSS measurements cannot qualify while the deployed runtime is the seed.

## Latest bounded verification

- Shell syntax, scoped diff hygiene, and the MCP/LSP native wrapper contract:
  PASS.
- Working and staged direct environment/runtime facade guards: PASS.
- Isolated clean bootstrap: Stage 2 and Stage 3 self-hosting PASS. Stage 4
  failed at `Map.keys`; GDB localized the call to async desugaring and the
  typed `rt_dict_keys` owner was restored. Post-fix full rebuild: NOT RUN due
  the three-cycle runaway guard.
- Pure-Simple runtime, Windows execution, latency, RSS, and executable system
  qualification: NOT RUN because the production runtime identity gate fails
  and this host has no PowerShell/Windows runtime.
