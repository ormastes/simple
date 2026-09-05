# CLI Run Output Owner Contract

> Raw stdout and stderr stay behind the CLI I/O owner module in Stage4.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Run Output Owner Contract

Raw stdout and stderr stay behind the CLI I/O owner module in Stage4.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/cli_run_output_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Raw stdout and stderr stay behind the CLI I/O owner module in Stage4.

## Scenarios

### CLI run output ownership

#### routes raw child stdout through the cli_ops owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- run a child process through the cli_ops owner
- child stdout and stderr arrive separated through the owner
   - Expected: code equals `0`
   - Expected: stdout equals `owner-routed`
   - Expected: stderr equals `oops`
- emit raw stdout through the owner adapter without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("run a child process through the cli_ops owner")
val (stdout, stderr, code) = _cli_process_run("/bin/sh", ["-c", "printf owner-routed; printf oops >&2"])
step("child stdout and stderr arrive separated through the owner")
# oracle: the owner must return the child's stdout verbatim and keep stderr separate
expect(code).to_equal(0)
expect(stdout).to_equal("owner-routed")
expect(stderr).to_equal("oops")
step("emit raw stdout through the owner adapter without error")
# oracle: the raw stdout adapter is callable at the owner boundary
_cli_print_raw("owner-adapter-probe")
```

</details>

#### owns adjacent stdout and stderr adapters in cli_ops

- call the stderr adapter at the owner boundary
- route a failing child through the same owner and observe its exit status
   - Expected: fail_code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("call the stderr adapter at the owner boundary")
# oracle: the stderr adapter is callable from the owning module's public surface
_cli_eprint("owner-stderr-probe")
step("route a failing child through the same owner and observe its exit status")
val (_out, _err, fail_code) = _cli_process_run("/bin/sh", ["-c", "exit 3"])
# oracle: the owner preserves the child's exit status unchanged
expect(fail_code).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `94fea05db62204b01a4e0717a3eea6e753834b55268858aeaf171938cfd8e2c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94fea05db62204b01a4e0717a3eea6e753834b55268858aeaf171938cfd8e2c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94fea05db62204b01a4e0717a3eea6e753834b55268858aeaf171938cfd8e2c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/io/cli_run_output_owner_spec.spl
mirror: doc/06_spec/01_unit/app/io/cli_run_output_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/cli_run_output_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/cli_run_output_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/cli_run_output_owner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/cli_run_output_owner_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes raw child stdout through the cli_ops owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/cli_run_output_owner_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns adjacent stdout and stderr adapters in cli_ops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
