# cli_os_spec

> Purpose: Prove that Top-level SimpleOS CLI wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_os_spec

Purpose: Prove that Top-level SimpleOS CLI wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/cli_os_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Top-level SimpleOS CLI wrapper.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Top-level SimpleOS CLI wrapper

#### dispatches os targets successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches os targets successfully
- Verify: dispatches os targets successfully
   - Expected: handle_os(["targets"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches os targets successfully")
step("Verify: dispatches os targets successfully")
# @req: REQ-APP-CLI-001
expect(handle_os(["targets"])).to_equal(0)
```

</details>

#### accepts os help aliases

- accepts os help aliases
- Verify: accepts os help aliases
   - Expected: handle_os(["help"]) equals `0`
   - Expected: handle_os(["--help"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts os help aliases")
step("Verify: accepts os help aliases")
expect(handle_os(["help"])).to_equal(0)
expect(handle_os(["--help"])).to_equal(0)
```

</details>

#### rejects unknown os subcommands with a non-zero exit code

- rejects unknown os subcommands with a non-zero exit code
- Verify: rejects unknown os subcommands with a non-zero exit code
   - Expected: handle_os(["unknown-subcommand"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown os subcommands with a non-zero exit code")
step("Verify: rejects unknown os subcommands with a non-zero exit code")
expect(handle_os(["unknown-subcommand"])).to_equal(1)
```

</details>

#### keeps the last valid --log occurrence across mixed forms

- keeps the last valid --log occurrence across mixed forms
- Verify: keeps the last valid --log occurrence across mixed forms
   - Expected: handle_os(["build", "--log=off", "--log", "on", "--arch=bogus"]) equals `1`
   - Expected: env_get("SIMPLE_OS_LOG_MODE") ?? "" equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the last valid --log occurrence across mixed forms")
step("Verify: keeps the last valid --log occurrence across mixed forms")
val prior = env_get("SIMPLE_OS_LOG_MODE")
val before = if prior == nil: "" else: prior
expect(handle_os(["build", "--log=off", "--log", "on", "--arch=bogus"])).to_equal(1)
expect(env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(before)
```

</details>

#### rejects bare --arch followed by another option

- rejects bare --arch followed by another option
- Verify: rejects bare --arch followed by another option
   - Expected: handle_os(["build", "--arch", "--log=off"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare --arch followed by another option")
step("Verify: rejects bare --arch followed by another option")
expect(handle_os(["build", "--arch", "--log=off"])).to_equal(1)
```

</details>

#### rejects bare --target followed by another option

- rejects bare --target followed by another option
- Verify: rejects bare --target followed by another option
   - Expected: handle_os(["build", "--target", "--log=off"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare --target followed by another option")
step("Verify: rejects bare --target followed by another option")
expect(handle_os(["build", "--target", "--log=off"])).to_equal(1)
```

</details>

#### rejects bare --scenario followed by another option

- rejects bare --scenario followed by another option
- Verify: rejects bare --scenario followed by another option
   - Expected: handle_os(["build", "--scenario", "--arch=x86_64"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare --scenario followed by another option")
step("Verify: rejects bare --scenario followed by another option")
expect(handle_os(["build", "--scenario", "--arch=x86_64"])).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-CLI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `72e5057f3b2c06a7d1630bdde778258671173015f6ad5ed16e06123bf35703c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72e5057f3b2c06a7d1630bdde778258671173015f6ad5ed16e06123bf35703c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72e5057f3b2c06a7d1630bdde778258671173015f6ad5ed16e06123bf35703c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli/cli_os_spec.spl
mirror: doc/06_spec/unit/app/cli/cli_os_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/cli_os_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/cli_os_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/cli_os_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/cli_os_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches os targets successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/cli_os_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts os help aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/cli_os_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown os subcommands with a non-zero exit code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
