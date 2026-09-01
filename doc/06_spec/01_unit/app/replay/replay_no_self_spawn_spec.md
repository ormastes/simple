# CLI entrypoints must not re-invoke themselves

> `simple replay <build-log>` once handled its unimplemented build-log branch by

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI entrypoints must not re-invoke themselves

`simple replay <build-log>` once handled its unimplemented build-log branch by

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/replay/replay_no_self_spawn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`simple replay <build-log>` once handled its unimplemented build-log branch by
re-invoking `./bin/simple replay <same args>`. Because the delegated child took
the same branch, it delegated again, forever: every process stayed alive blocked
in `wait`, producing ~124 live processes/min at ~62 MB RSS each (~8.4 GB/min)
until a 128 GB host was exhausted. `earlyoom` was configured with
`--prefer '^(simple|...)'`, so the resulting kills landed on *unrelated healthy*
`simple` processes -- Stage-3 bootstrap builds, test runs, MCP servers -- which
then presented as bare exit 143 with no diagnostic.

Bug: doc/08_tracking/bug/simple_replay_self_spawns_unbounded_process_chain_2026-08-10.md

## Scope and Preconditions

This is a SOURCE-INVARIANT spec. It deliberately does not execute the CLI: the
failure mode under test is an unbounded fork chain, and a spec that reproduced
it by running the binary would be the very host-exhaustion event it guards
against. Instead it reads the checked-in CLI entrypoint sources and asserts the
structural property whose absence caused the incident.

## Primary Workflow

An unimplemented (or not-found) CLI subcommand branch reports a terminating
diagnostic and returns a nonzero status. It never shells out to the same
subcommand of the same binary.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Self-spawn | A CLI branch invoking `bin/simple <its own subcommand>` |
| Terminating branch | Reports an error and returns; performs no delegation |

## Evidence and Provenance

Live re-verification 2026-08-17 with the exact incident argv:
`bin/simple replay missing-build-log.json` exits 1 printing
`log file not found: missing-build-log.json`, under a watchdog armed to kill at
>8 concurrent matching processes. The watchdog never fired and the process
count delta was 0.

## Recovery and Troubleshooting

If this spec fails, a CLI entrypoint has reintroduced self-delegation. Replace
the delegation with a terminating diagnostic; do not bound it with a depth
counter, which still multiplies processes.

## Compatibility and Limitations

Static/source-level. It cannot catch a self-spawn constructed dynamically from
a runtime-assembled command string.

## Scenarios

### replay CLI never self-spawns

#### the build-log branch reports instead of delegating to itself

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the build-log branch reports instead of delegating to itself
- Read the replay entrypoint source
- The unimplemented build-log branch states so and stops
- A missing log file is a terminating error, not a delegation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the build-log branch reports instead of delegating to itself")
step("Read the replay entrypoint source")
val source = read_cli_source("src/app/replay/main.spl")
step("The unimplemented build-log branch states so and stops")
expect_terminating_diagnostic(source, "build-log replay is not yet implemented")
step("A missing log file is a terminating error, not a delegation")
expect_terminating_diagnostic(source, "log file not found")
```

</details>

#### carries no invocation of its own subcommand

- carries no invocation of its own subcommand
- Read the replay entrypoint source
- No `bin/simple replay ...` self-invocation remains
   - Expected: spawns_own_subcommand(source, "replay") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("carries no invocation of its own subcommand")
step("Read the replay entrypoint source")
val source = read_cli_source("src/app/replay/main.spl")
step("No `bin/simple replay ...` self-invocation remains")
expect(spawns_own_subcommand(source, "replay")).to_equal(false)
```

</details>

#### keeps the incident rationale attached to the fixed branch

- keeps the incident rationale attached to the fixed branch
- Read the replay entrypoint source
- The bug record is cited where the self-spawn used to be
   - Expected: source contains `simple_replay_self_spawns_unbounded_process_chain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the incident rationale attached to the fixed branch")
step("Read the replay entrypoint source")
val source = read_cli_source("src/app/replay/main.spl")
step("The bug record is cited where the self-spawn used to be")
expect(source.contains("simple_replay_self_spawns_unbounded_process_chain")).to_equal(true)
```

</details>

#### the self-spawn detector actually detects a self-spawn

- the self-spawn detector actually detects a self-spawn
- Construct source that does delegate to its own subcommand
- The detector reports it
   - Expected: spawns_own_subcommand(bad, "replay") is true
- And a same-shaped call to a DIFFERENT subcommand is not a self-spawn
   - Expected: spawns_own_subcommand(bad, "build") is false
- A COMMENT quoting the old invocation is not a self-spawn
   - Expected: spawns_own_subcommand(commented, "replay") is false
- A help/usage string naming the subcommand is not a self-spawn
   - Expected: spawns_own_subcommand(usage, "replay") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the self-spawn detector actually detects a self-spawn")
step("Construct source that does delegate to its own subcommand")
val bad = "fn delegate(): shell(\"./bin/simple replay \" + target)"
step("The detector reports it")
expect(spawns_own_subcommand(bad, "replay")).to_equal(true)
step("And a same-shaped call to a DIFFERENT subcommand is not a self-spawn")
expect(spawns_own_subcommand(bad, "build")).to_equal(false)
step("A COMMENT quoting the old invocation is not a self-spawn")
val commented = "# never do: shell(\"./bin/simple replay \" + target)"
expect(spawns_own_subcommand(commented, "replay")).to_equal(false)
step("A help/usage string naming the subcommand is not a self-spawn")
val usage = "    print \"Usage: simple replay [options] <trace.srr>\""
expect(spawns_own_subcommand(usage, "replay")).to_equal(false)
```

</details>

### no CLI entrypoint delegates to its own subcommand

#### holds for every entrypoint known to have had the hazard

- holds for every entrypoint known to have had the hazard
- Check each entrypoint against its own subcommand name
- No entrypoint self-delegates
   - Expected: offenders.len() equals `0`
- The sweep examined a non-empty set (non-vacuity control)
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("holds for every entrypoint known to have had the hazard")
step("Check each entrypoint against its own subcommand name")
val entries = [
    ["src/app/replay/main.spl", "replay"],
]
var offenders: [text] = []
var i = 0
while i < entries.len():
    val path = entries[i][0]
    val subcommand = entries[i][1]
    val source = read_cli_source(path)
    if spawns_own_subcommand(source, subcommand):
        offenders.push(path)
    i = i + 1
step("No entrypoint self-delegates")
expect(offenders.len()).to_equal(0)
step("The sweep examined a non-empty set (non-vacuity control)")
expect(entries.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07f9bee28a105d5c1043f23ae42e459185e04514ac50927bffba7a5b907e21ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07f9bee28a105d5c1043f23ae42e459185e04514ac50927bffba7a5b907e21ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07f9bee28a105d5c1043f23ae42e459185e04514ac50927bffba7a5b907e21ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/replay/replay_no_self_spawn_spec.spl
mirror: doc/06_spec/01_unit/app/replay/replay_no_self_spawn_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=30
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
test/01_unit/app/replay/replay_no_self_spawn_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/replay/replay_no_self_spawn_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/replay/replay_no_self_spawn_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the build-log branch reports instead of delegating to itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/replay/replay_no_self_spawn_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries no invocation of its own subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/replay/replay_no_self_spawn_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the incident rationale attached to the fixed branch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
