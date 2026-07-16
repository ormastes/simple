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
The latest source lane also consolidates lint/fmt/fix ownership, adds actual
runner exit 3/4/124 probes, proves dependency-only cache invalidation, and
extracts deployment into a fault-injected atomic rollback helper. A final
three-way audit repaired the outcome probe arguments, routed CLI daemon calls
to the real owner, made dependency fingerprints content-based, restored lint's
public API use, scoped global lint gates to `--all`, corrected duplicate-check
path parsing, removed its dead parallel CLI, normalized `gen-lean` argv, and
hardened MCP/LSP wrapper probe correlation and atomic stamps. The deployed
runtime remains unavailable, so executable qualification is still blocked.

## Tool matrix

| Surface | Status | Bug / missing evidence | Root solution | Priority |
|---|---|---|---|---|
| Production runtime | BLOCKED | Stage 4 was found parsing 10,503 files before closure pruning; source fix is unverified because the final cycle stopped on a stale compiler-backfill guard | In a fresh session run one bounded `--full-bootstrap`, require closure-sized phase input, then admit and atomically deploy | P0 |
| Test runner | IMPLEMENTED | Failure/outcome/count/nesting, exact manifest correspondence, and deadline-bounded batch re-exec implemented | Run 1,000-example RSS evidence on pure runtime | P0 |
| Duplicate checker | IMPLEMENTED | Runtime qualification blocked by seed | Run hostile-path and measured benchmark probes on pure runtime | P0 |
| Lint | SOURCE FIXED | Focused/global ownership is correct; global gates still report 30 UI and 45 hot-loop violations | Repair classified violations, then qualify canonical fixtures | P1 |
| Format/fix | SOURCE FIXED | Duplicate handlers removed; executable dry-run proof awaits admitted runtime | Run canonical dry-run and write fixtures after admission | P1 |
| Check | BLOCKED | Command is parse/validation only; full type inference is not enforced | Implement enforcing type analysis, then qualify the production probe | P1 |
| CLI dispatch | IMPLEMENTED | Statistics are table-derived; runtime evidence blocked by seed | Execute inventory probe after admission | P1 |
| Test daemon | IMPLEMENTED | Real application owner and content-hash invalidation implemented; dynamic matrix blocked by runtime | Execute run/clean/hit/miss/same-size dependency invalidation after admission | P2 |
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

1. A clean admitted full-CLI runtime is unavailable. Phase profiling showed
   Stage 4 receiving 10,503 sources because the bootstrap entry path passed
   complete source roots before closure pruning. The source fix now seeds only
   the entry and reuses the driver's import resolver. Its final bounded build
   stopped before compilation because the compiler-backfill archive is stale
   and requires `--full-bootstrap`; the three-cycle cap is exhausted.
2. NFR-007 and NFR-009 evidence harnesses exist, but their production latency
   and RSS measurements cannot qualify while the deployed runtime is the seed.
3. `simple lint --all` correctly exposes 30 UI architecture and 45 hot-loop
   violations. Focused lint no longer fails on that unrelated repository debt;
   the global findings remain an explicit P1 cleanup lane.
4. `simple check` now states its actual parse/validation behavior. Enforced full
   type inference remains an open P1 implementation bug.

## Latest bounded verification

- Shell syntax, scoped diff hygiene, and the MCP/LSP native wrapper contract:
  PASS.
- Working and staged direct environment/runtime facade guards: PASS.
- Atomic deployment rollback fault injection: PASS, including restoration of
  an admitted prior binary and rejection of an unadmitted prior binary.
- Dependency-only shared-cache invalidation and actual runner exit 3/4/124
  probes: SOURCE IMPLEMENTED; executable verdict blocked by missing `bin/simple`
  in the isolated lane.
- MCP/LSP wrapper contract: PASS with fresh-layout log creation, explicit
  override rejection, content-hash cache invalidation, correlated protocol
  results, and atomic probe stamps.
- Native smoke evidence no longer accepts historical cache-hit log lines or an
  arbitrary candidate stamp; it requires current-run records and verified
  repair of the selected candidate's exact content-hash stamp.
- Isolated clean bootstrap: Stage 2 and Stage 3 self-hosting PASS in all three
  bounded cycles. Cycle 1 proved the typed `rt_dict_keys` repair and found the
  generic-close layout bug. Cycle 2 proved that repair and found missing
  `pub mod` grammar support. Cycle 3 proved both parser repairs, then Stage 4
  remained at about 100% CPU with RSS growing controllably from 1.7 GiB to
  2.9 GiB; it was stopped at the announced 25-minute ceiling with no full-CLI
  executable. No fourth cycle was run.
- Final bootstrap preflight: BLOCKED before compilation because stale compiler
  backfill requires `--full-bootstrap`; no fourth cycle was run.
- Pure-Simple runtime, Windows execution, latency, RSS, and executable system
  qualification: NOT RUN because the production runtime identity gate fails
  and this host has no PowerShell/Windows runtime.
