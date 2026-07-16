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
| Duplicate checker | IMPLEMENTED | Token child is deadline-bound and shell-free; native walker runtime parity and cosine cache mutation remain open | Repair `rt_dir_walk` symlink/file parity and cache mutation, then run hostile-path and measured probes | P0 |
| Lint | SOURCE FIXED | Focused/global ownership is correct; global gates still report 30 UI and 45 hot-loop violations | Repair classified violations, then qualify canonical fixtures | P1 |
| Format/fix | SOURCE FIXED | Duplicate handlers removed; executable dry-run proof awaits admitted runtime | Run canonical dry-run and write fixtures after admission | P1 |
| Check | BLOCKED | Command is parse/validation only; full type inference is not enforced | Implement enforcing type analysis, then qualify the production probe | P1 |
| CLI dispatch | IMPLEMENTED | Statistics are table-derived; runtime evidence blocked by seed | Execute inventory probe after admission | P1 |
| Test daemon | IMPLEMENTED | Requested waits no longer truncate at 60 seconds and dependency closure is no longer depth-truncated; dynamic matrix remains unqualified | Execute long-wait, deep dependency invalidation, and pinned-candidate cache probes after admission | P2 |
| SPipe/docgen | WARN | Executable spec/manual exist; generated-doc validation blocked by seed | Regenerate once with admitted runtime | P1 |
| MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P1 |
| LSP MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P0 |
| Windows CLI/MCP/LSP | IMPLEMENTED | Shared bounded SHA-256 and real-protocol admission; executable Windows evidence missing | Run `check-windows-tool-wrapper-contract.ps1` on Windows | P0 |
| `gen-lean` | IMPLEMENTED | Main dispatch reaches the distinct deadline-bound worker; runtime proof blocked by seed | Run bounded invalid-subcommand/worker probe | P2 |
| Lean proof checker | SOURCE FIXED | Configured timeout now reaches every Lake operation; executable fake-Lake timeout proof awaits admitted runtime | Run the focused shell-timeout spec and a fake-Lake check after admission | P1 |

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
   nested timeout, test-daemon invalidation, and `gen-lean` recursion. Source
   fixes now close the duplicate token-child deadline, hidden daemon 60-second
   ceiling, runner batch deadline, and `gen-lean` recursion; executable RSS and
   long-wait/cache qualification remain.

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

## Latest primary review decisions

- **Type inference:** do not flip the existing HM warn pass to fatal yet. The
  canonical driver is the right owner, but its checked-in burndown requires a
  stable stage-4 runtime, crash/blast measurement, and false-positive triage
  first. The lightweight production `check` contract stays truthful rather
  than importing a currently unqualified compiler graph.
- **UI isolation:** do not narrow the gate from all `rt_*` calls to rendering
  names. The architecture explicitly forbids every direct runtime call in app,
  example, and UI-library layers. Most of the 30 findings need existing
  env/process/file/time facades; platform-owner exceptions need exact reviewed
  ownership, while the RISC-V desktop entry retains genuine direct display
  bypasses.
- **CPU hot loops:** the 45 findings are not one mechanical baseline update.
  Browser pixel/span work, software blend/copy loops, and repeated compositor
  lookup are real owner-level debt; bounded parser/control/hardware polling
  loops need exact reason annotations only after the real hot paths move.
- **Compositor lookup:** repeated exact-ID scans now share one bounded
  `surface_index` owner. Z-order transforms, app/process group queries, hit
  testing, and rendering retain their intentional ordered scans. A focused
  identity/Z-order test covers present and missing IDs across focus, mutation,
  and removal.
- **Software spans:** do not route `self.buf` through the existing free-function
  span facade yet; the documented self-field mutation-loss bug makes that
  superficially minimal rewrite unsafe. Native blend additionally disagrees
  with `color.blend` for partial destination alpha. Both blockers and the exact
  parity coverage are recorded in the mutable-array extern bug.
- **Browser raster:** the reviewed next owner fixes are clipped iframe blit via
  `simd_blit_rect`, row fill ownership through `fill_span`, and piece-buffered
  numeric-entity decoding. Numeric decoding now uses buffered pieces with a
  focused repeated decimal/hexadecimal entity spec. Clipping and framebuffer
  mutation remain unmodified because their parity cannot be executed with an
  admitted runtime.
- **Daemon deadline:** `daemon_poll_result` already had the authoritative
  absolute deadline; its independent 600-attempt guard silently truncated all
  waits to about 60 seconds. The redundant guard is deleted, so every caller
  now receives the timeout it requested.
- **Duplicate token mode:** the fast child remains separate for its measured
  low latency, but it now runs through the existing 30-second timeout facade.
  Facade timeout `-1` is normalized to the truthful CLI timeout class `124`.
  Its file discovery now reuses `dir_walk_native`, preserving hostile path
  boundaries and deterministic sort order without shell/newline parsing.
  Runtime walker symlink/file parity and incremental-cache mutation remain
  separate tracked fixes.
- **Dependency closure:** the daemon and standalone runner now fingerprint the
  full cycle-safe import closure. The former magic depth-five ceiling silently
  omitted deeper dependencies and could return stale cache hits; the existing
  `seen` set already provides finite traversal.
- **Proof checker:** `CheckerConfig.timeout_ms` now reaches `LakeRunner`, and
  build/check/clean share the existing platform-aware process deadline through
  `shell_timeout`. Timeout markers remain visible as failed proof results.
- **Lint/fmt/fix review:** no import rewrite was accepted. `cli_ops` already
  re-exports `cli_lint_commands`, `run_commands.spl` has no duplicate handlers,
  and `simple.cmd` already resolves the admitted pure-Simple executable.
- **Duplicate cache ownership:** `TokenCacheManager` now has reference identity
  and owns writes behind capability-correct `me` methods. Compatibility free
  functions preserve callers while eliminating the W1006 value-copy path;
  persistent incremental mode remains separately disabled.
- **Test child execution:** daemon, worker-agent, and QEMU test children now
  share argv-preserving `process_run_timeout` execution. Test paths and QMP
  sockets are no longer shell-interpreted, and the requested deadline owns the
  child. GUI/service/hardware children use the same owner with scoped parent
  environment restoration while dispatch remains synchronous. Remote terminal
  execution and QMP/OpenOCD protocol shell sites remain explicit follow-ups.
- **Native walker parity:** no wrapper-only patch was accepted. Traversal occurs
  entirely inside `rt_dir_walk`, and every available Simple type probe follows
  symlinks, so cycle prevention and file-only parity require coordinated C,
  Rust SFFI, interpreter, and Windows runtime-owner changes.
- **Session adapter reachability:** the old registry retained only each
  concrete adapter's inert `.base`, so production start/execute/reset/stop
  calls never reached QEMU, container, service, GUI, or hardware code. The
  broker now stores typed optional adapters and dispatches directly by kind;
  production registration retains concrete state while unit brokers stay
  dependency-free.
- **Session resource identity:** deterministic scheduler keys now hash every
  matching field, including reset policy, while each new lease adds a broker
  instance suffix. Fresh concurrent acquisitions can no longer target the same
  container name or QMP socket, and metadata cannot inject path separators or
  shell syntax into resource IDs.
- **Container transport:** Docker/Podman detection, lifecycle, inspection,
  reset, execution, and teardown now share structured argv plus bounded host
  execution. Fixed resource limits remain explicit argv entries; test paths,
  images, and lease IDs never pass through a shell.

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
- Daemon CLI, runner client, launcher, and child execution now share one
  `SIMPLE_BINARY`-first selector; the system spec also runs every production
  command through the pinned candidate.
- Windows contract coverage now includes isolated fake-native negative cases
  for sidecars, correlated protocol errors, stamp invalidation, and explicit
  MCP/LSP overrides; execution still requires a Windows PowerShell host.
- Shared daemon-selector caller/forbidden-shell source contracts, qualification
  binary routing, Windows fake-contract markers, and owned whitespace: PASS.
- Compositor exact-ID lookup consolidation and its focused behavior spec:
  SOURCE IMPLEMENTED; executable verdict blocked by the unavailable admitted
  pure-Simple runtime.
- Numeric entity piece-buffering and repeated decimal/hexadecimal Draw IR spec:
  SOURCE IMPLEMENTED; executable verdict blocked by the same runtime gate.
- Daemon requested-deadline ownership and bounded duplicate token-child source
  contracts: PASS by scoped source inspection; dynamic timeout behavior is NOT
  RUN because no admitted runtime exists.
- Fast duplicate native discovery, full cycle-safe test dependency closure,
  checker-to-Lake deadline propagation, and the shared shell-timeout facade:
  PASS by scoped source contracts and diff hygiene. Their focused Simple specs
  are NOT RUN because no admitted runtime exists.
- Token-cache reference ownership and shared argv-safe daemon/agent/QEMU child
  execution: SOURCE IMPLEMENTED; executable cache/hostile-path/timeout verdicts
  are NOT RUN because no admitted runtime exists.
- Concrete adapter dispatch, unique safe session instances, and container argv
  transport: SOURCE IMPLEMENTED with focused pure helper/session contracts;
  executable daemon/container verdict is NOT RUN without an admitted runtime.
- Environment-bearing GUI/service/hardware child execution now shares bounded
  argv execution and restores the parent environment; focused hostile-value
  and restoration coverage is SOURCE IMPLEMENTED but NOT RUN.
- New Simple unit/system behavior and the PowerShell contract: NOT RUN because
  no admitted pure-Simple runtime or PowerShell host exists. Previously passed
  global gates were not repeated after their session limit.
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
