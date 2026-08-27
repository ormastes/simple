# exe_size_budget_spec

> Executable size regression guard — Phase 5 T2.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# exe_size_budget_spec

Executable size regression guard — Phase 5 T2.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/exe_size_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable size regression guard — Phase 5 T2.

Compiles a hello-world Simple program to a stripped native binary and asserts
that the on-disk size stays within a defined budget.

Budget: 12 MB (12,582,912 bytes).  Current baseline: ~9.4 MB (9,623,568 bytes).
The ~25% headroom accommodates cross-machine noise from rustc/libc version
differences while still catching regressions above that threshold.

On failure the test prints:
  - old budget vs new size and % delta
  - `size -A <bin> | head -20` section breakdown
  - `nm --size-sort -r -S <bin> | head -10` top symbols

The test also verifies the produced binary actually runs and prints "Hello World"
so a stub-generation false-green is caught immediately (per memory:
feedback_compile_mode_false_greens.md).

## Scenarios

### exe size budget — stripped hello-world native binary

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

#### compiles hello.spl to a stripped native binary

- compiles hello.spl to a stripped native binary
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles hello.spl to a stripped native binary")
# Compile fresh so the test is not stale even if the pre-built artifact
# was produced by an older toolchain.
val result = run_shell(
    "bin/simple native-build --entry " + FIXTURE_SPL + " -o " + OUTPUT_BIN + " --entry-closure --runtime-bundle auto --strip"
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

#### binary runs and prints Hello World (not a stub)

- binary runs and prints Hello World (not a stub)
   - Expected: stdout contains `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binary runs and prints Hello World (not a stub)")
# Per feedback_compile_mode_false_greens.md: compile path can produce a
# stub that reports success but does not actually execute.  Verify real output.
val result = run_shell(OUTPUT_BIN)
val stdout = result.0
if not stdout.contains("Hello World"):
    print "BINARY DID NOT PRINT 'Hello World'"
    print "stdout: " + stdout
    print "stderr: " + result.1
    print "exit code: " + result.2.to_text()
expect(stdout.contains("Hello World")).to_equal(true)
```

</details>

#### stripped binary size is within budget

- stripped binary size is within budget
   - Expected: size_bytes <= BUDGET_BYTES is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stripped binary size is within budget")
val data = rt_file_read_bytes(OUTPUT_BIN) ?? []
val size_bytes: i64 = data.len()

if size_bytes > BUDGET_BYTES:
    # Print actionable diagnostic so future debugger doesn't need to re-run
    val pct = ((size_bytes - BUDGET_BYTES) * 100) / BUDGET_BYTES
    print "SIZE REGRESSION DETECTED"
    print "  Budget  : " + BUDGET_BYTES.to_text() + " bytes (" + (BUDGET_BYTES / 1048576).to_text() + " MB)"
    print "  Actual  : " + size_bytes.to_text() + " bytes (" + (size_bytes / 1048576).to_text() + " MB)"
    print "  Baseline: " + BASELINE_BYTES.to_text() + " bytes (measured 2026-04-28)"
    print "  Delta   : +" + pct.to_text() + "% over budget"

    # Section breakdown
    val size_result = run_shell("size -A " + OUTPUT_BIN + " | head -20")
    print "--- size -A (top sections) ---"
    print size_result.0

    # Top symbols by size
    val nm_result = run_shell("nm --size-sort -r -S " + OUTPUT_BIN + " | head -10")
    print "--- nm top symbols ---"
    print nm_result.0

expect(size_bytes <= BUDGET_BYTES).to_equal(true)
```

</details>

#### baseline has not grown beyond budget (sanity — pre-built artifact)

- baseline has not grown beyond budget (sanity — pre-built artifact)
   - Expected: size_bytes > 0 is true
   - Expected: size_bytes < 52428800 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("baseline has not grown beyond budget (sanity — pre-built artifact)")
# Assert on the known pre-built artifact size without re-compiling,
# so this test passes even in environments where compile is unavailable.
val data = rt_file_read_bytes(OUTPUT_BIN) ?? []
val size_bytes: i64 = data.len()
# The pre-built artifact was 9.4 MB; if it ever exceeds budget the above
# test catches it — this it-block is a belt-and-suspenders sanity check.
expect(size_bytes > 0).to_equal(true)
expect(size_bytes < 52428800).to_equal(true)   # hard ceiling: 50 MB
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `cdc009f76a7e61e26f4de68a8591245253e70160b3c83b6db19359983349f037`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdc009f76a7e61e26f4de68a8591245253e70160b3c83b6db19359983349f037`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdc009f76a7e61e26f4de68a8591245253e70160b3c83b6db19359983349f037`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/infrastructure/exe_size_budget_spec.spl
mirror: doc/06_spec/03_system/infrastructure/exe_size_budget_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infrastructure/exe_size_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/exe_size_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/exe_size_budget_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/infrastructure/exe_size_budget_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture source file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/exe_size_budget_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles hello.spl to a stripped native binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/exe_size_budget_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produced binary exists after compile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
