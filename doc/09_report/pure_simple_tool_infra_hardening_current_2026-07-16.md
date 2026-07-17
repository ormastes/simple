# Pure-Simple tool and infrastructure hardening status

Date: 2026-07-17

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
hardened MCP/LSP wrapper probe correlation and atomic stamps. The latest
remaining-tool audit additionally activated the shared process governor,
removed cosine candidate truncation, made tool writes atomic and checked,
bounded remaining runner subprocesses, and quoted MCP CLI inputs. It also
invalidated earlier optimistic daemon and formatter status: both retain
release-blocking correctness defects. The deployed runtime remains unavailable,
so executable qualification is still blocked.

## Tool matrix

| Surface | Status | Bug / missing evidence | Root solution | Priority |
|---|---|---|---|---|
| Production runtime | BLOCKED | Stage 4 was found parsing 10,503 files before closure pruning; source fix is unverified because the final cycle stopped on a stale compiler-backfill guard | In a fresh session run one bounded `--full-bootstrap`, require closure-sized phase input, then admit and atomically deploy | P0 |
| Test runner | PARTIAL | POSIX parallel children are tracked; resource-limited children now honor the requested soft deadline with one five-second TERM-to-KILL grace. Sequential/limited/fork/QEMU children remain synchronously untracked; Windows parallel capture fails closed | Move every execution mode onto an interruptible tracked process owner, add process-group/parent-death containment, then run signal/timeout/RSS evidence | P0 |
| Duplicate checker | SOURCE FIXED | Production token mode uses the canonical detector; cosine candidate progress is time-throttled instead of reading RSS and writing stderr per pair; exact/cosine line gates share one tokenizer-derived signal prefix; runtime/performance qualification remain | Run focused token/cosine fixtures and benchmark the canonical path with an admitted runtime | P1 |
| Lint | SOURCE GUARDED | Production CLI delegates to the canonical file linter; dead duplicate paths are deleted; hot-loop BYTE names are file-scoped; MCP performance fails closed without an owner; global gates report 25 UI and 41 hot-loop violations | Add one repository-scanner owner for the four MCP rules, repair classified violations, then run focused fixtures | P1 |
| Format/fix | SOURCE GUARDED | Writes are atomic and checked; output passes a CoreLexer equivalence gate or fails closed; empty files and generic casts are safe; the corrupting indentation-repair prepass is deleted | Replace remaining heuristic transforms incrementally with token-gap edits, then run executable preservation/idempotence fixtures | P0 |
| Check | PARTIAL | Driver API Check stops after fatal HIR analysis; production parse/policy workers now apply SSpec guidance equally in human and JSON modes. CLI can still false-green HIR-invalid code and may delegate to the seed | Retain CLI policy checks, route semantics through `driver_api_core.check_file`, consolidate duplicate workers, remove seed delegation only after direct-path latency/RSS qualification | P1 |
| CLI dispatch | IMPLEMENTED | Statistics are table-derived; runtime evidence blocked by seed | Execute inventory probe after admission | P1 |
| Test daemon | SOURCE FIXED | CLI/client share the full daemon protocol; local, container, remote, lightweight, and agent paths now retain canonical passed/failed/skipped counts and fail closed on malformed outer summaries; dynamic qualification remains | Run the authored local/session/count-cache/timeout/stop protocol fixtures with an admitted runtime | P0 |
| SPipe/docgen | WARN | Executable spec/manual exist; generated-doc validation blocked by seed | Regenerate once with admitted runtime | P1 |
| MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P1 |
| LSP MCP wrapper | IMPLEMENTED | Native-first hash/protocol contract and content-addressed probe cache passed statically | Collect protocol latency/RSS evidence | P0 |
| MCP CLI passthrough | SOURCE FIXED | Binary and every JSON-derived argument are shell quoted; structured argv is still preferable when response capture supports it | Run hostile apostrophe/metacharacter protocol fixtures after runtime admission | P0 |
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
3. `simple lint --all` correctly exposes 25 UI architecture and 41 hot-loop
   violations. Focused lint no longer fails on that unrelated repository debt;
   the global findings remain an explicit P1 cleanup lane.
4. `simple check` now states its actual parse/validation behavior. Enforced full
   type inference remains an open P1 implementation bug.
5. The default test-daemon rendezvous, lifecycle bypass, result parsing, and
   cache count retention are source-fixed. Runtime protocol, shutdown, adapter,
   count-cache, and timeout evidence remains NOT RUN, so daemon claims are not
   yet dynamically qualified.
6. Formatter edits still infer syntax from raw text, but semantics-changing
   proposals are now rejected at the shared `format_source` boundary. Dynamic
   preservation/idempotence evidence remains NOT RUN.

## Remaining-tool audit backlog

| Rank | Defect | Concrete solution |
|---|---|---|
| P1 | Formatter heuristics are contained but not token-gap-native | Replace them incrementally with edits limited to lexer-approved whitespace gaps |
| P1 | Lint global gates still report classified UI/hot-loop violations; MCP-perf has per-source rules but no repository-scanner owner | Add the aggregate owner, repair violations, and run focused policy fixtures with an admitted runtime |
| P1 | Signal cleanup covers only tracked parallel children | Move sequential, limited, fork, daemon, doctest, and QEMU children onto an interruptible tracked owner; contain descendant groups separately |
| P1 | Signal runtime availability is not portable | Guard POSIX `sigaction`, report installation truthfully on Windows, and qualify Ctrl-C separately from POSIX HUP/TERM |
| P2 | Direct broker callers can retain inactive leases | Production request/execution paths now reject and remove inactive leases; refactor broker-only tests before enforcing active-only retention inside `SessionBroker.acquire` |

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
- **CPU hot loops:** the 41 findings are not one mechanical baseline update.
  Browser pixel/span work, software blend/copy loops, and repeated compositor
  lookup are real owner-level debt; bounded parser/control/hardware polling
  loops need exact reason annotations only after the real hot paths move.
- **Hot-loop BYTE ownership:** the gate formerly collected `[u8]` identifiers
  across the entire designated set, so `data[...]` in one file could inherit an
  unrelated byte declaration from another. Detection now pairs each name with
  its declaring file. Positive and cross-file-negative fixtures pass directly;
  the real gate still reports 41 LOOP/SUBSTR findings and no BYTE false hit.
- **Lint MCP performance:** the known inert `build lint --mcp-perf` subprocess
  is removed. `--mcp-perf` and `--all` now fail closed with an explicit owner-gap
  error instead of false-greening. The four real per-source rules still need one
  repository-scanner aggregate before the option can become operational.
- **UI facade duplication:** the unreferenced
  `src/lib/common/ui/host_winit_surface.spl` duplicate is deleted. An
  absence/canonical-owner regression retains all seven host-window operations
  in `std.nogc_sync_mut.io.window_winit`; the direct gate drops from 30 to 29
  new files without changing its baseline. Remaining findings require owner
  migrations rather than duplicate removal.
- **Check entry I/O boundary:** the lightweight worker resolver now uses the
  exact `std.nogc_sync_mut.io.file_ops.file_exists` leaf instead of declaring a
  raw runtime hook. Release-binary selection and fallback behavior are
  unchanged; the UI isolation gate loses one unbaselined app file.
- **WM daemon runtime boundary:** daemon serving and health recovery now use
  exact file, process, environment, PID, and time facades. Both wait paths use
  the native `sffi.system.sleep_ms` wrapper, avoiding the shell-backed app sleep
  path in the 16 ms serve loop. The isolation gate loses two unbaselined files,
  from 28 to 26 new findings, without changing the 541-file baseline.
- **SimpleOS toolchain CI argv boundary:** the CI builder now uses `get_args`
  from its existing `std.io_runtime` dependency instead of declaring a raw CLI
  hook. Argument scanning and target selection are unchanged; the isolation
  gate loses one more unbaselined app file, from 26 to 25 new findings.
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
- **Duplicate token ownership:** the low-latency fast script remains an
  explicit audit tool with native deterministic discovery, but the production
  CLI no longer launches it. Token and cosine gates use the canonical detector's
  one-per-file tokenizer signal prefix, so comments and string literals cannot
  create code-shaped candidates; exact keys retain leading indentation. Runtime
  walker parity, canonical-path performance, and incremental-cache mutation
  remain separate qualification items.
- **Duplicate cosine progress:** candidate totals are unknown until oversized
  buckets, same-file pairs, and repeated cross-bucket pairs are removed. The
  comparator now passes the shared unknown-total sentinel and renders a
  count-only, interval-throttled update. `--progress` and `--verbose` no longer
  read `/proc/self/status` and emit stderr for every comparison; the existing
  completion line still reports the exact final count.
- **Formatter empty files:** `file_read` uses empty text for both a zero-byte
  file and read failure. The canonical formatter now checks existence first,
  and `fix` reuses its existing existence guard instead of rejecting valid
  empty files.
- **Check enforcement:** the smallest enforcing owner is the existing
  `driver_api_core.check_file` path. Its Check mode now returns after fatal HIR
  lowering and before monomorphization. Production routing is not activated
  until an admitted runtime proves startup, latency, and RSS and the lightweight
  SSpec/HGL/concurrency/hygiene policies remain intact.
- **Check JSON parity:** both the active worker and reachable in-process
  fallback now evaluate SSpec command-block guidance independently of output
  mode. Human mode prints the existing redirect; JSON suppresses prose but
  counts one failed file, so mode selection cannot turn the same source green.
- **Runner signals:** one idempotent callback now owns each signal, and the
  tracked parallel loop plus both governor waits cooperatively dispatch pending
  POSIX signals. Failed kills remain tracked instead of disappearing from
  cleanup state. Sequential/limited/fork/daemon/doctest/QEMU waits are still
  synchronous and untracked; fatal-crash cleanup additionally needs process-
  group or parent-death containment. Source comments no longer claim otherwise.
- **Runner limited deadlines:** the canonical bounded process owner no longer
  adds five seconds before also applying GNU timeout's five-second kill grace.
  Positive millisecond deadlines use overflow-safe ceiling conversion, so
  1001–1999 ms no longer expire at one second and a one-second request no
  longer waits six seconds before TERM.
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
  environment restoration while dispatch remains synchronous. Remote terminal,
  QMP, and OpenOCD operations now use their shared protocol/process owners.
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
- **QEMU session ownership:** production status, admission snapshots, cleanup,
  and shutdown now use the typed `SessionBroker` that owns real adapter PID/QMP
  leases. The never-acquired legacy `QemuBroker` was removed from the daemon;
  failed production acquisitions are rejected and removed immediately.
- **Container transport:** Docker/Podman detection, lifecycle, inspection,
  reset, execution, and teardown now share structured argv plus bounded host
  execution. Fixed resource limits remain explicit argv entries; test paths,
  images, and lease IDs never pass through a shell.
- **Container runner backend:** standalone container detection, image lookup,
  test execution, image build, version, and volume cleanup now use bounded
  structured argv. Runtime duration uses the real runtime clock instead of
  the former constant-zero placeholder.
- **Composite hardware runner:** WCH-Link discovery/status uses bounded argv,
  and STM32H7 logging/sleeping use native output/timing owners instead of
  launching shells.
- **Runner lifecycle:** tracked containers now launch/stop through bounded argv
  with an ownership label instead of returning a fake ID. Cleanup only selects
  that label, and heartbeat timestamps use the runtime clock instead of
  constant stub values.
- **Remote terminal transport:** the terminal owner now exposes bounded
  execution for SSH and Telnet. Telnet uses one absolute deadline across all
  reads, and the remote-PC adapter quotes the test path before sending the
  unavoidable remote shell command. T32 SWD forwards the requested deadline
  to TRACE32, relay scripts use bounded structured argv, and production
  daemon startup registers canonical SDN SSH/Telnet configs by metadata target.
  Remote test paths are restricted to traversal-free repo-relative
  `test/*.spl` paths before command construction.
- **Hardware protocol transport:** OpenOCD process startup and every TRACE32
  profile now use structured argv with explicit deadlines. OpenOCD commands
  share the bounded Telnet owner, and program paths reject command-language
  metacharacters before transmission.
- **QEMU protocol transport:** the daemon adapter now reuses the persistent QMP
  client for status, snapshots, and restore; process/file/directory facades
  replace its remaining shell calls, and each short-lived QMP fd is closed.
- **Remaining shared roots:** the process governor now enforces its configured
  cap with atomic admission and underflow-safe release. File overwrite uses the
  runtime atomic-write owner, and formatter/fix propagate write failure.
  Duplicate cosine analysis retains every inverted-index candidate instead of
  silently sampling 320 blocks.
- **MCP CLI boundary:** retain the existing static command registry, but quote
  the binary and every JSON-derived value at the single shell boundary. This is
  the smallest compatible injection fix until response capture accepts argv.
- **Parallel runner boundary:** POSIX capture passes argv through fixed shell
  positional parameters and `exec`; it never joins arguments into source text.
  Windows fails closed and failed spawns are not waited/untracked. Platform and
  CPU discovery now use native runtime owners instead of subprocess probes.
- **Tracked child timeout:** the lifecycle owner now waits, kills, and releases
  timed-out children as one operation. Parallel collection uses only that owner;
  a child is never untracked while still running, and runtime `-2` becomes the
  canonical runner timeout `-1`.
- **Runner summary parsing:** only canonical `Results: N total, P passed, F
  failed` lines own aggregate counts. Test-authored `Results:` output is ignored,
  and the last canonical outer summary wins.
- **Full daemon owner:** the CLI and runner client now start the same full
  daemon protocol through a reaped short-lived launcher. Requests retain their
  IDs and requested child deadlines; session metadata selects the broker, and
  every acquired lease is stopped, reset, or released after execution.
- **Formatter containment:** do not port the Rust formatter or extend the
  duplicate-check tokenizer. The shared pure-Simple `format_source` owner now
  fingerprints CoreLexer tokens, exact literal slices, comments, and raw brace
  gaps before accepting output. Any semantic drift returns an error before the
  atomic write path. Blind `<`/`>` spacing is removed because cast generics such
  as `value as Box<T>` require adjacency and whitespace-only fingerprints cannot
  distinguish those delimiters from comparisons.
- **Formatter indentation:** the removed `fix_indentation` prepass dedented
  after `return` and again before `else`/`elif`, moving valid branches outside
  their function while leaving the token fingerprint unchanged. The existing
  `format_code_lines` pass already preserves source-derived indentation, so no
  replacement heuristic is needed.

## Latest bounded verification

- Remaining-tool focused source contracts, including atomic process admission,
  full cosine candidate retention, bounded child execution, atomic writes, MCP
  quoting, and non-placeholder focused specs: PASS. Dynamic Simple tests are
  NOT RUN because no admitted runtime exists.
- Full-daemon entry, canonical configuration, request-ID response routing,
  timeout transport, and broker lifecycle source contracts: SOURCE
  IMPLEMENTED; executable daemon protocol and adapter verdicts are NOT RUN.
- Formatter token/literal/comment/raw-gap equivalence, generic-cast adjacency,
  branch indentation, and idempotence fixtures:
  SOURCE IMPLEMENTED; executable verdict is NOT RUN without an admitted
  pure-Simple runtime.
- Lint canonical severity/profile policy, unique shared-rule collection, and
  monotonic fileless `--all` aggregation: SOURCE IMPLEMENTED. The unreferenced
  722-line parallel implementation is deleted; executable verdict is NOT RUN
  without an admitted pure-Simple runtime.
- Tracked-wait timeout cleanup and canonical runner-summary precedence have
  focused source specs; executable verdict is NOT RUN without an admitted
  pure-Simple runtime.
- Duplicate exact-window indexing, lexer-derived signal filtering,
  content-hash cache freshness, unsupported mode rejection, and missing-target
  failure: SOURCE IMPLEMENTED; executable verdict is NOT RUN without an
  admitted pure-Simple runtime.
- Default semantic adjacent-function extraction with one-line docs: SOURCE
  IMPLEMENTED; executable verdict is NOT RUN without an admitted runtime.
- Exact duplicate indentation preservation, code-shaped signal filtering, and
  shifted-window collapse: SOURCE IMPLEMENTED; executable verdict is NOT RUN.
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
- OpenOCD/Telnet, TRACE32 argv, and remote SSH/Telnet deadline ownership are
  SOURCE IMPLEMENTED with focused hostile-input contracts; executable verdicts
  are NOT RUN because no admitted runtime exists.
- Standalone container-runner argv boundaries and real duration accounting are
  SOURCE IMPLEMENTED with hostile-value coverage; executable Docker/Podman
  verdict is NOT RUN without an admitted runtime.
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
