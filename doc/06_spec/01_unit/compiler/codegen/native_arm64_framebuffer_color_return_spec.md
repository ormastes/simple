# Native ARM64 framebuffer color construction preserves all four channels

> This is the focused reproducer for the SimpleOS ARM64 QEMU failure that reached

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native ARM64 framebuffer color construction preserves all four channels

This is the focused reproducer for the SimpleOS ARM64 QEMU failure that reached

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This is the focused reproducer for the SimpleOS ARM64 QEMU failure that reached
RAMFB and then faulted in `Color.rgb` before `desktop-ready`.  The interpreter
control is useful, but the subprocess native build is the acceptance oracle.

## Scenarios

### native ARM64 framebuffer Color return ABI

#### preserves channels in the interpreter control

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves channels in the interpreter control
- Construct the same four-u8 color returned by Color.rgb
   - Expected: color.r equals `17`
   - Expected: color.g equals `31`
   - Expected: color.b equals `47`
   - Expected: color.a equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves channels in the interpreter control")
step("Construct the same four-u8 color returned by Color.rgb")
val color = Arm64FramebufferColor.rgb(17, 31, 47)
expect(color.r).to_equal(17)
expect(color.g).to_equal(31)
expect(color.b).to_equal(47)
expect(color.a).to_equal(255)
```

</details>

#### preserves channels in a native entry-closure binary

- preserves channels in a native entry-closure binary
- Build and execute the exact small-struct return shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves channels in a native entry-closure binary")
step("Build and execute the exact small-struct return shape")
val output = native_build_and_run_color()
expect(output.contains("BUILD-FAILED")).to_be(false)
expect(output).to_contain("4\n17\n31\n47\n255")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87ac69c9e4554935df754b556478ea9a930e9ef2a37288f357cab77896d9dbc2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87ac69c9e4554935df754b556478ea9a930e9ef2a37288f357cab77896d9dbc2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87ac69c9e4554935df754b556478ea9a930e9ef2a37288f357cab77896d9dbc2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves channels in the interpreter control' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_arm64_framebuffer_color_return_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves channels in a native entry-closure binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
