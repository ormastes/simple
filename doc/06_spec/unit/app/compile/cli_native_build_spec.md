# cli_native_build_spec

> Verifies the cli native build behaviour end to end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_native_build_spec

Verifies the cli native build behaviour end to end.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/compile/cli_native_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the cli native build behaviour end to end.
Audience: engineers maintaining this component and its specs.

## Scenarios

### cli_native_build parser hardening

#### rejects a trailing bare --log flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify: rejects a trailing bare --log flag
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects a trailing bare --log flag")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log"])).to_equal(1)
```

</details>

#### rejects an empty inline --log value

- Verify: rejects an empty inline --log value
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log="]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects an empty inline --log value")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log="])).to_equal(1)
```

</details>

#### rejects bare --log followed by another option

- Verify: rejects bare --log followed by another option
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects bare --log followed by another option")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"])).to_equal(1)
```

</details>

#### rejects typoed --log-prefixed flags

- Verify: rejects typoed --log-prefixed flags
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects typoed --log-prefixed flags")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"])).to_equal(1)
```

</details>

#### rejects a single invalid inline --log value

- Verify: rejects a single invalid inline --log value
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects a single invalid inline --log value")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"])).to_equal(1)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

- Verify: rejects an invalid later --log value instead of keeping an earlier valid one
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: rejects an invalid later --log value instead of keeping an earlier valid one")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"])).to_equal(1)
```

</details>

#### accepts a valid llvm-lib --log flag and forwards it before later build failure

- Verify: accepts a valid llvm-lib --log flag and forwards it before later build failure
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=off", "--entry", "missing-entry.spl"]) equals `1`
   - Expected: env_get("SIMPLE_OS_LOG_MODE") ?? "" equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILE-CliNativeBuild-001
step("Verify: accepts a valid llvm-lib --log flag and forwards it before later build failure")
val prior = env_get("SIMPLE_OS_LOG_MODE")
val before = if prior == nil: "" else: prior
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=off", "--entry", "missing-entry.spl"])).to_equal(1)
expect(env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(before)
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
- `REQ-COMPILE-CliNativeBuild-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a018199e8b0898ec3f9dc34e9c76f8441af82ae58b480c7032080dbf3a468cb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a018199e8b0898ec3f9dc34e9c76f8441af82ae58b480c7032080dbf3a468cb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a018199e8b0898ec3f9dc34e9c76f8441af82ae58b480c7032080dbf3a468cb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/compile/cli_native_build_spec.spl
mirror: doc/06_spec/unit/app/compile/cli_native_build_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/compile/cli_native_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/compile/cli_native_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/compile/cli_native_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/compile/cli_native_build_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/compile/cli_native_build_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a trailing bare --log flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/compile/cli_native_build_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty inline --log value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/compile/cli_native_build_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects bare --log followed by another option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
