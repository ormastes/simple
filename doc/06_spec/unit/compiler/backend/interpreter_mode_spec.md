# interpreter_mode_spec

> Purpose: Prove that Interpreter Mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interpreter_mode_spec

Purpose: Prove that Interpreter Mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/interpreter_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Interpreter Mode.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Interpreter Mode

#### creates the default hybrid JIT config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates the default hybrid JIT config
- Verify: creates the default hybrid JIT config
   - Expected: config.mode equals `JitMode.Auto`
   - Expected: config.backend equals `auto`
   - Expected: config.jit_threshold equals `10`
   - Expected: config.verbose is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates the default hybrid JIT config")
step("Verify: creates the default hybrid JIT config")
# @req: REQ-COMP-INTERPRETER-MODE-001
val config = JitInterpreterConfig(
    mode: JitMode.Auto,
    backend: "auto",
    jit_threshold: 10,
    verbose: false
)

expect(config.mode).to_equal(JitMode.Auto)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(10)
expect(config.verbose).to_equal(false)
```

</details>

#### creates an always-interpret config

- creates an always-interpret config
- Verify: creates an always-interpret config
   - Expected: config.mode equals `JitMode.AlwaysInterpret`
   - Expected: config.backend equals `auto`
   - Expected: config.verbose is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an always-interpret config")
step("Verify: creates an always-interpret config")
val config = JitInterpreterConfig(
    mode: JitMode.AlwaysInterpret,
    backend: "auto",
    jit_threshold: 999999,
    verbose: false
)

expect(config.mode).to_equal(JitMode.AlwaysInterpret)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_be_greater_than(1000)
expect(config.verbose).to_equal(false)
```

</details>

#### creates an always-jit config

- creates an always-jit config
- Verify: creates an always-jit config
   - Expected: config.mode equals `JitMode.AlwaysJit`
   - Expected: config.backend equals `auto`
   - Expected: config.jit_threshold equals `0`
   - Expected: config.verbose is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an always-jit config")
step("Verify: creates an always-jit config")
val config = JitInterpreterConfig(
    mode: JitMode.AlwaysJit,
    backend: "auto",
    jit_threshold: 0,
    verbose: false
)

expect(config.mode).to_equal(JitMode.AlwaysJit)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(0)
expect(config.verbose).to_equal(false)
```

</details>

#### creates a thresholded auto-jit config

- creates a thresholded auto-jit config
- Verify: creates a thresholded auto-jit config
   - Expected: config.mode equals `JitMode.Auto`
   - Expected: config.backend equals `auto`
   - Expected: config.jit_threshold equals `1`
   - Expected: config.verbose is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a thresholded auto-jit config")
step("Verify: creates a thresholded auto-jit config")
val config = JitInterpreterConfig(
    mode: JitMode.Auto,
    backend: "auto",
    jit_threshold: 1,
    verbose: false
)

expect(config.mode).to_equal(JitMode.Auto)
expect(config.backend).to_equal("auto")
expect(config.jit_threshold).to_equal(1)
expect(config.verbose).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-INTERPRETER-MODE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d677ae9ce2c8c8846252bbe69b753f3cc6cd1e5af592952b3c14e02efa6911d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d677ae9ce2c8c8846252bbe69b753f3cc6cd1e5af592952b3c14e02efa6911d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d677ae9ce2c8c8846252bbe69b753f3cc6cd1e5af592952b3c14e02efa6911d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/interpreter_mode_spec.spl
mirror: doc/06_spec/unit/compiler/backend/interpreter_mode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/interpreter_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/interpreter_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/interpreter_mode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/interpreter_mode_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates the default hybrid JIT config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/interpreter_mode_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an always-interpret config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/interpreter_mode_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an always-jit config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
