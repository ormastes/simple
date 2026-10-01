# string_codegen_regression_spec

> The fixture prints one println-terminated marker line per check; the exact

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# string_codegen_regression_spec

The fixture prints one println-terminated marker line per check; the exact

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/string_codegen_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Examples

The fixture prints one println-terminated marker line per check; the exact
expected stdout is `EXPECTED_STDOUT` below. A regression on any one of the
four bug classes changes at least one marker line (or, for the print bug,
corrupts arbitrary bytes anywhere in the blob), so the whole-blob equality
check in "stdout exactly matches golden output" is the strongest oracle and
the per-line checks pinpoint which bug class came back.

## Scenarios

### string/text native-codegen regression guard

#### fixture source file exists

- fixture source file exists
   - Expected: rt_file_exists(FIXTURE_SPL) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture source file exists")
expect(rt_file_exists(FIXTURE_SPL)).to_equal(true)
```

</details>

#### compiles the fixture to a native binary

- compiles the fixture to a native binary
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles the fixture to a native binary")
val result = run_shell(
    "env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry " + FIXTURE_SPL +
    " -o " + OUTPUT_BIN + " --entry-closure --clean"
)
if result.2 != 0:
    print "COMPILE STDOUT: " + result.0
    print "COMPILE STDERR: " + result.1
expect(result.2).to_equal(0)
```

</details>

#### produced binary exists after compile

- produced binary exists after compile
   - Expected: rt_file_exists(OUTPUT_BIN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produced binary exists after compile")
expect(rt_file_exists(OUTPUT_BIN)).to_equal(true)
```

</details>

#### native binary exits 0 -- every internal rt_exit(N) self-check passed (rc encodes which check failed: 1=concat.len, 2=text==+fused-bool, 3=text== negative control, 4=fill-literal, 5=push, 6=interpolation)

- native binary exits 0 -- every internal rt_exit(N) self-check passed (rc encodes which check failed: 1=concat.len, 2=text==+fused-bool, 3=text== negative control, 4=fill-literal, 5=push, 6=interpolation)
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native binary exits 0 -- every internal rt_exit(N) self-check passed (rc encodes which check failed: 1=concat.len, 2=text==+fused-bool, 3=text== negative control, 4=fill-literal, 5=push, 6=interpolation)")
val result = run_shell(OUTPUT_BIN)
if result.2 != 0:
    print "UNEXPECTED EXIT CODE: " + result.2.to_text()
    print "stdout: " + result.0
    print "stderr: " + result.1
expect(result.2).to_equal(0)
```

</details>

#### concat `.len()` reads the tagged string's real length, not the RtCoreString header byte

- concat `.len()` reads the tagged string's real length, not the RtCoreString header byte
   - Expected: stdout contains `CATLEN:6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concat `.len()` reads the tagged string's real length, not the RtCoreString header byte")
# Pre-fix, rt_strlen read the tagged pointer directly and returned 3
# (stopped at the header's reserved-field NUL) instead of 6.
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("CATLEN:6"):
    print "concat .len() wrong; stdout: " + stdout
expect(stdout.contains("CATLEN:6")).to_equal(true)
```

</details>

#### print/println of a `+`-concat result outputs the real string, not a tagged-pointer fragment

- print/println of a `+`-concat result outputs the real string, not a tagged-pointer fragment
   - Expected: stdout contains `ab\n`
   - Expected: stdout contains `helloworld\n`
   - Expected: stdout contains `mixed\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("print/println of a `+`-concat result outputs the real string, not a tagged-pointer fragment")
# Pre-fix, this line would contain the RtCoreString header bytes
# (garbage/short fragment) instead of "ab", and the same for
# "helloworld" and "mixed" below -- checked here as one blob so a
# header-byte corruption anywhere is caught even if it doesn't
# happen to break line-splitting.
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("ab\n"):
    print "MISSING 'ab' concat-print line; stdout: " + stdout
expect(stdout.contains("ab\n")).to_equal(true)
if not stdout.contains("helloworld\n"):
    print "MISSING 'helloworld' println-concat line; stdout: " + stdout
expect(stdout.contains("helloworld\n")).to_equal(true)
if not stdout.contains("mixed\n"):
    print "MISSING 'mixed' literal+var concat-print line; stdout: " + stdout
expect(stdout.contains("mixed\n")).to_equal(true)
```

</details>

#### #148 untyped text `==` with fused `and` evaluates true for equal content

- #148 untyped text `==` with fused `and` evaluates true for equal content
   - Expected: stdout contains `EQ_AND_LEN:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("#148 untyped text `==` with fused `and` evaluates true for equal content")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("EQ_AND_LEN:true"):
    print "text == + fused bool did not report true; stdout: " + stdout
expect(stdout.contains("EQ_AND_LEN:true")).to_equal(true)
```

</details>

#### #148 untyped text `==` correctly rejects unequal content (no bitwise-identity false-positive)

- #148 untyped text `==` correctly rejects unequal content (no bitwise-identity false-positive)
   - Expected: stdout contains `NEG:false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("#148 untyped text `==` correctly rejects unequal content (no bitwise-identity false-positive)")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("NEG:false"):
    print "text == wrongly reported equal for distinct content; stdout: " + stdout
expect(stdout.contains("NEG:false")).to_equal(true)
```

</details>

#### #149 [\

- #149 [\
   - Expected: stdout contains `FILLED:xyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("#149 [\")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("FILLED:xyz"):
    print "fill-literal content lost/corrupted; stdout: " + stdout
expect(stdout.contains("FILLED:xyz")).to_equal(true)
```

</details>

<details>
<summary>Advanced: #149 .push() on an untyped [text] array survives a concat-drop loop</summary>

#### #149 .push() on an untyped [text] array survives a concat-drop loop

- #149 .push() on an untyped [text] array survives a concat-drop loop
   - Expected: stdout contains `PUSHED:pqr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("#149 .push() on an untyped [text] array survives a concat-drop loop")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("PUSHED:pqr"):
    print ".push() content lost/corrupted; stdout: " + stdout
expect(stdout.contains("PUSHED:pqr")).to_equal(true)
```

</details>


</details>

#### string interpolation mixed with `+` concat produces the correct combined text

- string interpolation mixed with `+` concat produces the correct combined text
   - Expected: stdout contains `n=3 tail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string interpolation mixed with `+` concat produces the correct combined text")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("n=3 tail"):
    print "interpolation+concat mismatch; stdout: " + stdout
expect(stdout.contains("n=3 tail")).to_equal(true)
```

</details>

#### stdout exactly matches golden output (whole-blob oracle, no stray/garbage bytes)

- stdout exactly matches golden output (whole-blob oracle, no stray/garbage bytes)
   - Expected: stdout equals `EXPECTED_STDOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stdout exactly matches golden output (whole-blob oracle, no stray/garbage bytes)")
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if stdout != EXPECTED_STDOUT:
    print "STDOUT MISMATCH"
    print "  expected: " + EXPECTED_STDOUT
    print "  actual  : " + stdout
expect(stdout).to_equal(EXPECTED_STDOUT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92004e8146738e19ecac8cda8248d17931ab8ce3382ea8c000c5542d3a1294a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92004e8146738e19ecac8cda8248d17931ab8ce3382ea8c000c5542d3a1294a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92004e8146738e19ecac8cda8248d17931ab8ce3382ea8c000c5542d3a1294a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/compiler/string_codegen_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/string_codegen_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/string_codegen_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/string_codegen_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/string_codegen_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/string_codegen_regression_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture source file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/string_codegen_regression_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles the fixture to a native binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/string_codegen_regression_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produced binary exists after compile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
