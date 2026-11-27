# BuildRunner / SOSIX end-to-end implementation and verification plan

Date: 2026-10-29. Source baseline: release/1.0.0 `17c632ff6a0`.
State: **end-to-end acceptance BLOCKED**. This is an execution plan for the
existing goal, not permission to rebuild Phase 2 or weaken containment.

## Evidence at the planning boundary

| Surface | Observed state | Consequence |
|---|---|---|
| Pinned pure-Simple P2 | SHA-256 `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`; original `/Users/ormastes/wt/release-phase2-review/build/verify/pure-spl-aliasfix-p2-20261025-02/stage2-simple-aliasfix` removed; prior bounded search found no matching retained copy | Native source-matched Simple builds and SSpec execution cannot be qualified with that producer. **Do not rebuild P2.** |
| Actual BuildRunner attempt | `/private/tmp/real-buildrunner-retry-20261029-vg0rlds8/state/attempts/hello/1/local/compiler.not-started.sdn`: `SIMPLE-NO-CHILD-STARTED-1`, `exact process observation V4 unavailable` | This is a real admission refusal, not a compiled or executed Hello. Its pins record monitor policy and no worker OS memory enforcement request. |
| Darwin V4 | `runtime_process_observation_v4_darwin_selfcheck.c` expects unavailable caps and ENOTSUP across start/poll/cancel/collect/ACK | Directory pins, image snapshots and broker transport do not install strict V4. Preserve the refusal. |
| Darwin tree boundary | `check-sosix-darwin-strict-tree.shs --require-strict` deliberately returns 78 after negative escape evidence | A process group, kqueue observation or same-UID snapshot cannot prove permanent all-descendant containment. |
| Linux V4 | Existing [group-admission report](../../08_tracking/bug/buildrunner_v4_group_provider_admission_2026_10_28.md) records LeaderOnly support and ProcessGroup/Tree refusal | cgroup parser/start/cleanup fixtures are useful component evidence, not a qualified group V4 provider. |
| Windows ownership | V2 foundation report leaves V4 ENOTSUP and native Windows qualification unexecuted; newer active V3/V4 work requires its own merged revision and receipts | Do not infer Windows-native success from macOS cross-compilation, stubs or non-Windows exit 77. |
| Test runner | Supported output is text/doc/SDN; SDN needs scoped-environment V4. `run-native-aot-suite.shs` still requested `--json` and its validator required terminal JSON | This change repairs the text invocation/validation pair. No new compiler is needed for its boundary tests. |
| Runner coverage | [Current report](../../08_tracking/bug/runner_coverage_missing_native_probe_lowering_2026_10_28.md) leaves current entrypoint and fixture unqualified; six explicit decisions are a partial denominator | Do not call these six sites whole-runner coverage. Generic native probe insertion/lowering remains separate unfinished work. |

Earlier evidence is historical unless its source, runtime, producer, provider,
test and invocation identities match the candidate. A merged PR is source
integration, not execution evidence. Local temporary paths above are discovery
hints, not durable release artifacts; missing evidence stays missing.

## Dependency graph and concrete work

Two independent streams can progress now: host-native component tests and
receipt/orchestration contract tests. Positive Simple E2E requires both an
admitted surviving producer and a qualified host process owner.

| Work item | Dependencies | Implementation / verification task | Completion proof |
|---|---|---|---|
| E00 — preserve identities | None | Capture exact release head, source patch, tool/runtime hashes and prior failure receipts in a fresh evidence directory. Register each changed input; preserve old attempts. | Immutable identity manifest and original nonzero outcomes; no mutable source/cache shared with active jobs. |
| E01 — restore usable producer access | E00 | Recover the exact pinned bytes from an already-existing trusted artifact/archive with original lineage. If unavailable, keep blocked; a different already-existing producer needs its own admission and must not inherit the old hash. | Byte hash, executable permissions, receipt/runtime compatibility and actual compiler command identity agree. No P2 build command executed. |
| E02 — qualify host owner | E00 | Complete selected OS-enforced image/cwd and descendant ownership mechanism; wire its start/poll/cancel/collect/frozen/ACK boundary into V4. Refuse absent authority before acquisition/spawn. | Host-adversarial matrix below passes on the real target OS; no lost cleanup ticket or falsely empty tree. Capability enabled only with the installed implementation. |
| E03 — repair evidence route | E00 | Use supported `--format text` for native suite execution and strict file/aggregate/invocation validation. Audit remaining phase wrappers using retired terminal JSON separately. | New text positive controls and all negative controls pass; retired JSON cannot satisfy this route. This patch completes the focused boundary repair. |
| E04 — qualify current runner | E01, E02 for scoped native process routes, E03 | Build source-matched full CLI/test-runner with the surviving admitted producer and existing native backend route. Exercise production entry, worker, output, timeout, continuation and cache owners. | Executed SSpec logs, native executable headers/hashes, precise compiler argv and nonzero red-control exits. Source listing is not binary-owned enumeration. |
| E05 — BuildRunner Hello gate | E01, E02 | Build manager/writer/worker from the frozen source and execute four Hello linkage forms for LLVM and Cranelift using production BuildRunner. Enforce task memory where requested. | Eight independent manager-verified results with matching worker memory receipts, bundles, native outputs and exact stdout/exit. An unsupported form is BLOCKED, not PASS. |
| E06 — compiler/interpreter/loader products | E04, successful producer Hello | Build the existing six aggregate native products (three subsystems × two backends), enumerate each executable through its actual supported interface, then execute all cases. Repair existing aggregation/listing if absent. | Six product identities plus real binary-owned inventories and executed case totals; per-file suite diagnostics do not substitute for six aggregates. |
| E07 — Phase 3 then Phase 4 | E05, prerequisite producer admission | Run existing managed schedule and complete configured inventories. Before each produced compiler becomes a producer, compile and execute Hello with that exact image. Continue independent failures. | Both backend cohorts; P3 self-rebuild and P4 products have separate lineage, invocation, output and test receipts. Never restart P2. |
| E08 — final review and landing | Applicable completed rows | Review exact source diff, SPipe manuals, native evidence and all unresolved rows; land scoped reviewed fixes. | No fabricated count or skipped/blocked conversion. End-to-end completion remains false until all required dependent rows have real evidence. |

E01 is an artifact dependency, not a repair-by-rebuild task. If it remains
blocked, complete E02/E03's independent host work and preserve E04–E07 as
unexecuted. A Rust seed can have separately authorized diagnostic evidence;
it never substitutes for E01 or qualifies pure-Simple/SPipe execution.

## Host process failure matrix

Each row needs an actual production owner call plus an independent oracle.
Fault-injected host fixtures prove state transitions; repeat essential ownership
cases with real processes before enabling host capability.

| ID | Cases | Required oracle and failure behavior |
|---|---|---|
| H01 — no-authority start | Missing provider, unsupported scope, malformed request, wrong image/cwd identity | No child PID/ticket acquired; no executable pin attempted where capability preflight applies; durable no-child receipt, not a successful task. |
| H02 — exact start identity | Image replacement after pin, path rename, cwd symlink/race, argv spaces/empty/Unicode, isolated environment | Executed bytes and cwd match owner pins; exact argv/env arrive at child. Refusal must retain any post-spawn cleanup authority. |
| H03 — descendant containment | `setsid`, `setpgid`, double fork, leader exits first, concurrent fork during cancel, migration attempt | A real enforced boundary contains every descendant; leader wait or group-kill success alone cannot produce tree-empty. |
| H04 — launch failures | Image/cwd acquire failure, assignment failure, resume failure, exec failure, first clock failure | Pre-spawn failure has no child; post-spawn failure retains an owned cleanup ticket until exact terminal cleanup. |
| H05 — capture | Both streams fill pipes, embedded NUL, split UTF-8, zero/small byte budgets, absent destination, held descendant writer | No deadlock or unsigned-budget overflow. Retained and delivered byte counts are exact; unread bytes and live writers prevent premature collection. |
| H06 — deadlines/signals | Deadline expires during startup/poll/cleanup; repeated EINTR; term ignored; cancellation repeated | Absolute deadlines never restart. Failed kill retries preserve pending intent; bounded cleanup failure preserves owner state. |
| H07 — terminal ownership | Leader reap before descendants, stale/reused PID, malformed/duplicate population observations, wrong owner, collector crash | Only exact kernel-owned wait plus enforced empty membership can establish terminal. Numeric PID scans cannot release ownership. |
| H08 — frozen/ACK | Duplicate collect, changed digest, wrong ticket/request/kind, replay, wrong owner, ACK transport failure | Frozen bytes repeat exactly. Invalid ACK keeps ownership; only the exact acknowledged receipt releases resources once. |
| H09 — resource policy | Enforced limit hit, monitor-only receipt, peak unavailable, incorrect metric, limit mismatch | Preserve requested policy, enforced bytes and metric meaning. Job commit is not RSS; monitor/watchdog cannot satisfy OS memory enforcement. |
| H10 — concurrency and recovery | 1/2/N leases, two waves exceeding historical capacity, cancel during poll, owner restart, abandoned partial attempt | No token/handle/FD leaks, cross-owner release or stranded admission. Recovery inventories every outstanding owner and refuses unsupported recovery. |

Platform-specific acceptance adds:

- **macOS:** test loader-time injection before `main`, immutable image identity,
  broker authentication/FD inheritance, and an actually enforced descendant
  boundary. The current direct-child broker, coalition observations and trusted
  snapshot profile are narrower evidence. Keep strict V4 blocked until the
  selected mechanism supports arbitrary required compiler descendants.
- **Linux:** real delegated cgroup authority with migration denied, atomic
  placement, valid strict population observations, exact child/image identity,
  failed `cgroup.kill` retries and removal failures. A writable same-credential
  cgroup path leaves containment unqualified. Run ptrace-dependent fixtures on
  supported native execution rather than treating emulator failures as success.
- **Windows:** real Windows SDK/runtime, suspended creation, restricted handle
  list, Job assignment and breakaway rejection, exact process handles, Unicode
  argv/env/cwd, concurrent capture/cancel/collect and Job memory receipts. V2 or
  V3 functionality is not V4 qualification.
- **FreeBSD/SimpleOS:** first report actual supported capability; use native
  guest execution for any claimed provider. Add a separate native linkage
  adapter before extending the Hello matrix, whose current host target model
  covers Linux/Darwin/Windows. Unsupported hosts must not be relabeled Linux.

Existing entry points include `check-sosix-darwin-{process,strict-tree,
broker-admission,bound-image,uid-process}.shs`,
`check-process-v4-group-admission.shs`, and the Windows owned-process scripts.
Consult each script's exit contract: exit 77/78 and an unavailable-provider
fixture PASS are not positive process-provider admission.

## BuildRunner, runner and bootstrap matrix

| ID | Required scenarios | Acceptance evidence |
|---|---|---|
| B01 | Missing producer/runtime/template/manager, wrong hashes, runtime changes during staging, unsupported target ABI | Refuse before task execution; preserve reason and no-child state. Recovery cannot silently pick another producer. |
| B02 | One source; two objects; static archive; shared library, for LLVM and Cranelift | Actual compile and explicit link inputs where applicable; real native executable runs with exact Hello output and exit zero. |
| B03 | Manager exit zero without receipt, wrong task/attempt/worker, missing memory receipt, monitor-only policy, wrong enforced bytes | Each remains FAIL. Manager verification text alone never admits output. |
| B04 | Bundle identity/backend/phase/route mismatch; output hash mismatch; duplicate fields/members; traversal/symlink/device; oversized members | Reject before extracting into published evidence. Result binds exact artifact and producer; fresh private destinations. |
| B05 | Cold build, qualified cache hit, stale cache, changed source/tool/runtime, missing output parent, output execute mode, partial recovery | Correct task identity and cache authority; runnable published output. A cached row is not a fresh native-test execution. |
| R01 | Green, deliberate failing assertion, timeout, crash, empty/feature-gated spec, missing Results, zero case count | Correct nonzero exits and separate executed/failed/blocked counts; no vacuous PASS. |
| R02 | Current text output, duplicate verdicts/Results, skipped/pending/cached suffixes, count disagreement, missing/extra invocation or execution | Production validator rejects incomplete/ambiguous evidence and retains failed artifacts. Supported text route is implemented in this patch. |
| R03 | Source roots order, backend selection, library mode, compiler pin, invocation argv, separate writable caches | Real emitted invocation agrees with executable and configured producer; no interpreter or seed fallback on native failure. |
| R04 | Sequential files, bounded concurrency, independent failure continuation, interrupted campaign and resumed attempts | Failure latch never resets; all runnable independent rows collected; counts distinguish discovered/buildable/executed/unexecuted. |
| R05 | Six explicit runner decisions: green/red/empty, count three, entry opt-in/opt-out, descendant env removal, existing output/symlink refusal | Actual current fixture and entrypoint; preserve six-site denominator. Partial report remains `whole_runner_coverage: false`. |
| R06 | Generic coverage insertion/lowering, short circuiting, exactly-once effects, optimization/cache identity, uncovered declarations | Actual compiler-produced decision/condition probes. Source inventories, manual counters and six-site R05 cannot satisfy this row. |
| P01 | Six subsystem aggregates, real binary enumeration and complete execution | Inventory bound to each executable; all required compiler core/HIR/MIR, interpreter and loader cases counted once. |
| P02 | P3 self-rebuild, P4 both producer cohorts, binary tools and libraries, compiler Hello before dependent work | Exact producer lineage; complete configured inventories and actual invocation records. Phase-directory names are not phase admission. |

Use the existing `test --native-backend=llvm|cranelift` route; preserve
`--assert-ran --no-cache --no-db --no-session-daemon --sequential
--keep-artifacts --verbose --format text` for the focused native suite wrapper.
`--mode=native` alone may mean an SMF path and is insufficient evidence.
The suite validator's transcript is a consistency check, not an authenticated
process transcript: live acceptance also needs production manager receipts
and an admitted runner, not synthetic stdout or image-header fixtures.

Relevant existing SSpec includes
`test/01_unit/app/buildrunner/{hello_native_run_v1,output_mode,
partial_recovery_cleanup,stage_trace_v1}_spec.spl`, common V4 receipt specs,
`test/02_integration/lib/io/process_observation_cleanup_v4_spec.spl`, and
`test/01_unit/app/test_runner/runner_self_coverage_spec.spl`.
Inventory fail-fast placeholders explicitly before execution. For each changed
SSpec run `simple spipe-docgen <spec> --output doc/06_spec --no-index` with an
admitted surviving runtime and require zero stubs. An authored manual with
blocked docgen stays labeled authored; it is not a generated-manual PASS.

## Resource limits and stop rules

- Keep one compiler-producing task active on this Mac until measured memory
  justifies more. Default focused fixture budget: two compiler threads,
  2 GiB task memory, 120 seconds per native build, 15 seconds per fixture
  executable, 1 MiB captured output per stream. These are proposed bounded
  verification defaults; preserve any explicitly authorized active profile.
- Do not apply these defaults to an existing live manager or silently replace
  an already selected worker count. Historic 40-worker Windows diagnostics
  require their original host budget and receipt; they are not a Mac default.
- E05 uses the adapter's actual whole-task bound of `8 × per-command timeout
  + 30s`, with the manager invocation allowance separately recorded. The
  enforced memory receipt must match the configured byte limit exactly.
- Finite focused campaign: 1,800 seconds. Existing full phase campaign: 7,200
  seconds unless explicitly configured otherwise. Retain deadline/resource
  failures and run healthy independent rows within the same finite inventory.
- Keep a minimum 2 GiB free disk before builds and cap retained logs; output
  volume or disk refusal is a failed/blocked row, never permission to erase
  another session's workspace or pinned producer.
- At most six verify/fix cycles per feature, including prior attempts; every
  retry needs changed code or new evidence. Do not repeat green checks in the
  same session. Stop at an unchanged external dependency and work independent
  rows; never loop producer discovery or rebuild the prohibited P2.

## Checks implemented and executed in this patch

1. `native_aot_suite_contract_test.py`: five unittest methods, 41 fixture cases
   across text acceptance for two backends, 23 transcript rejections, nine
   identity/artifact failures, six argv/inventory failures and one wrapper
   failure-propagation test. The original code produced three expected red
   assertions (two JSON-only validator failures and retired wrapper flag).
   The repaired production wrapper/validator passes all five methods.
2. `hello_sanity_buildrunner_test.py`: 14 unittest methods pass. New matrices
   cover all eight lane identity fields, eight unsafe archive members, member
   count/duplicate fields, two kernel-enforcement metric pairs, 16 memory
   mismatches, missing/extra/malformed memory fields and 12 result-identity
   mutations. Existing missing-receipt and four-form/two-backend cases remain.
3. `bootstrap_native_aot_evidence_contract_test.shs`: existing two-backend and
   identity/argv fixture suite passes on the supported text protocol. Its
   temporary directory is canonicalized for macOS `/var` versus `/private/var`
   identity; the validator's private-artifact boundary remains strict.
4. Perl/shell syntax and scoped diff whitespace checks pass. These are host
   fixture checks only. No P2 build, Simple native suite or live strict V4
   success was executed by this patch. No SSpec was edited or generated.

Local logs: `/private/tmp/astra-native-aot-red.log`,
`/private/tmp/astra-native-aot-green.log`, `/private/tmp/astra-hello-admission.log`.
The commands in the changed test files reproduce the fixture results without
the missing compiler. Preserve durable copies with the eventual run manifest;
temporary log existence is not an acceptance prerequisite for the source fix.

Merge owner: Astra planning lane; exact-diff reviewer: root or its assigned
reviewer. Host implementation owners remain their existing lanes. New parallel
agent work is not required by this plan. Final E2E reviewer must reconcile
the complete matrix and block admission on missing live evidence.
