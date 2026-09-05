# cli_spec

> Purpose: Prove that SimpleOS CLI parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_spec

Purpose: Prove that SimpleOS CLI parser.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SimpleOS CLI parser.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### SimpleOS CLI parser

#### rejects a trailing bare --log flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a trailing bare --log flag
- Verify: rejects a trailing bare --log flag
   - Expected: handle_os(["build", "--log"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a trailing bare --log flag")
step("Verify: rejects a trailing bare --log flag")
# @req: REQ-OS-001
expect(handle_os(["build", "--log"])).to_equal(1)
```

</details>

#### rejects an empty inline --log value

- rejects an empty inline --log value
- Verify: rejects an empty inline --log value
   - Expected: handle_os(["build", "--log="]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty inline --log value")
step("Verify: rejects an empty inline --log value")
expect(handle_os(["build", "--log="])).to_equal(1)
```

</details>

#### rejects bare --log followed by another option

- rejects bare --log followed by another option
- Verify: rejects bare --log followed by another option
   - Expected: handle_os(["build", "--log", "--arch=x86_64"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare --log followed by another option")
step("Verify: rejects bare --log followed by another option")
expect(handle_os(["build", "--log", "--arch=x86_64"])).to_equal(1)
```

</details>

#### rejects typoed --log-prefixed flags

- rejects typoed --log-prefixed flags
- Verify: rejects typoed --log-prefixed flags
   - Expected: handle_os(["build", "--logg", "off"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects typoed --log-prefixed flags")
step("Verify: rejects typoed --log-prefixed flags")
expect(handle_os(["build", "--logg", "off"])).to_equal(1)
```

</details>

#### rejects a single invalid inline --log value

- rejects a single invalid inline --log value
- Verify: rejects a single invalid inline --log value
   - Expected: handle_os(["build", "--log=maybe"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a single invalid inline --log value")
step("Verify: rejects a single invalid inline --log value")
expect(handle_os(["build", "--log=maybe"])).to_equal(1)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

- rejects an invalid later --log value instead of keeping an earlier valid one
- Verify: rejects an invalid later --log value instead of keeping an earlier valid one
   - Expected: handle_os(["build", "--log=on", "--log", "maybe"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid later --log value instead of keeping an earlier valid one")
step("Verify: rejects an invalid later --log value instead of keeping an earlier valid one")
expect(handle_os(["build", "--log=on", "--log", "maybe"])).to_equal(1)
```

</details>

#### rejects a trailing bare --arch flag

- rejects a trailing bare --arch flag
- Verify: rejects a trailing bare --arch flag
   - Expected: handle_os(["build", "--arch"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a trailing bare --arch flag")
step("Verify: rejects a trailing bare --arch flag")
expect(handle_os(["build", "--arch"])).to_equal(1)
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

#### rejects a trailing bare --target flag

- rejects a trailing bare --target flag
- Verify: rejects a trailing bare --target flag
   - Expected: handle_os(["build", "--target"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a trailing bare --target flag")
step("Verify: rejects a trailing bare --target flag")
expect(handle_os(["build", "--target"])).to_equal(1)
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

#### rejects a trailing bare --scenario flag

- rejects a trailing bare --scenario flag
- Verify: rejects a trailing bare --scenario flag
   - Expected: handle_os(["build", "--scenario"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a trailing bare --scenario flag")
step("Verify: rejects a trailing bare --scenario flag")
expect(handle_os(["build", "--scenario"])).to_equal(1)
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

#### rejects a trailing bare --board flag

- rejects a trailing bare --board flag
- Verify: rejects a trailing bare --board flag
   - Expected: handle_os(["test", "--board"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a trailing bare --board flag")
step("Verify: rejects a trailing bare --board flag")
expect(handle_os(["test", "--board"])).to_equal(1)
```

</details>

#### rejects bare --board followed by another option

- rejects bare --board followed by another option
- Verify: rejects bare --board followed by another option
   - Expected: handle_os(["test", "--board", "--arch=riscv64"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare --board followed by another option")
step("Verify: rejects bare --board followed by another option")
expect(handle_os(["test", "--board", "--arch=riscv64"])).to_equal(1)
```

</details>

#### rejects unsupported board names

- rejects unsupported board names
- Verify: rejects unsupported board names
   - Expected: handle_os(["test", "--board=arm32"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported board names")
step("Verify: rejects unsupported board names")
expect(handle_os(["test", "--board=arm32"])).to_equal(1)
```

</details>

#### rejects unsupported x86 alias board names

- rejects unsupported x86 alias board names
- Verify: rejects unsupported x86 alias board names
   - Expected: handle_os(["test", "--board=x86"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported x86 alias board names")
step("Verify: rejects unsupported x86 alias board names")
expect(handle_os(["test", "--board=x86"])).to_equal(1)
```

</details>

#### restores SIMPLE_OS_LOG_MODE after a failed canonical build path

- restores SIMPLE_OS_LOG_MODE after a failed canonical build path
- Verify: restores SIMPLE_OS_LOG_MODE after a failed canonical build path
   - Expected: handle_os(["build", "--log=off", "--arch=bogus"]) equals `1`
   - Expected: rt_env_get("SIMPLE_OS_LOG_MODE") ?? "" equals `prior`
   - Expected: rt_env_set("SIMPLE_OS_LOG_MODE", prior) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores SIMPLE_OS_LOG_MODE after a failed canonical build path")
step("Verify: restores SIMPLE_OS_LOG_MODE after a failed canonical build path")
val prior = rt_env_get("SIMPLE_OS_LOG_MODE") ?? ""
expect(handle_os(["build", "--log=off", "--arch=bogus"])).to_equal(1)
expect(rt_env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(prior)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", prior)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b70d1c958a101dc7cfe9f31d2121aebab53b278963afaad6c9f51fbd95e7fac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b70d1c958a101dc7cfe9f31d2121aebab53b278963afaad6c9f51fbd95e7fac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b70d1c958a101dc7cfe9f31d2121aebab53b278963afaad6c9f51fbd95e7fac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/cli_spec.spl
mirror: doc/06_spec/unit/os/cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/cli_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a trailing bare --log flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/cli_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty inline --log value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/cli_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects bare --log followed by another option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
