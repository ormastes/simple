# native_capturing_lambda_closure_conversion_spec

> Capturing lambdas on the native path: closure conversion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_capturing_lambda_closure_conversion_spec

Capturing lambdas on the native path: closure conversion.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Capturing lambdas on the native path: closure conversion.

Bug native_capturing_lambda_closure_conversion_2026-08-22. Pre-fix, on
`native-build`, `val add_k = \\v: v + k; add_k(10)` died with
`MIR lowering error: undefined variable v`, and a lambda literal passed as a
call argument `apply(\\v: v + k, 10)` with
`E-MIR-EXPR-Lambda ... closure conversion has not run`.

The closure-conversion pass DID exist (`lower_lambda_value`: lift to
`__lambda_lift_<n>`, captures materialized by value into an `rt_closure_new`
env, read back with `rt_closure_get_capture`, called through the
`rt_closure_func_ptr` diamond). It was written against the dead `local_map`
while identifier resolution had moved to `bind_local`/`find_local`, so every
capture lookup missed: the lift declined (nil -> E-MIR-EXPR-Lambda) and the
beta-reduced inline path bound its params into a map nobody read.

Capture semantics are BY VALUE at creation (oracle: `var n = 5; val f = \\x:
x + n; n = 100; f(3)` -> 8), matching the seed's rt_closure_set_capture copy.

The MIR-level examples run in-process and are cheap; the native example
shells out ONCE for the whole six-shape fixture (a native-build is ~2-3 min)
and compares its stdout against the interpreter lane on the same source.

## Scenarios

### capturing lambda MIR closure conversion

#### lowers a val-bound capturing lambda call without 'undefined variable'

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a val-bound capturing lambda call without 'undefined variable'


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a val-bound capturing lambda call without 'undefined variable'")
val src = "fn run() -> i64:\n    val k = 5\n    val add_k = \\v: v + k\n    add_k(10)\n"
val errs = errors_joined(lowering_errors(src))
expect_not(errs.contains("undefined variable"))
expect_not(errs.contains("E-MIR-EXPR-Lambda"))
```

</details>

#### materializes a capturing lambda call argument as an rt_closure_new env

- materializes a capturing lambda call argument as an rt_closure_new env
   - Expected: has_function_prefix(mir, "__lambda_lift_") is true
   - Expected: count_direct_calls_named(mir, "rt_closure_new") equals `1`
   - Expected: count_direct_calls_named(mir, "rt_closure_set_capture") equals `1`
   - Expected: count_direct_calls_named(mir, "rt_closure_get_capture") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes a capturing lambda call argument as an rt_closure_new env")
val src = "fn apply(f: fn(i64) -> i64, x: i64) -> i64:\n    f(x)\nfn run() -> i64:\n    val k = 5\n    apply(\\v: v + k, 10)\n"
val errs = errors_joined(lowering_errors(src))
expect_not(errs.contains("E-MIR-EXPR-Lambda"))
val mir = lower_source(src)
expect(has_function_prefix(mir, "__lambda_lift_")).to_equal(true)
expect(count_direct_calls_named(mir, "rt_closure_new")).to_equal(1)
expect(count_direct_calls_named(mir, "rt_closure_set_capture")).to_equal(1)
expect(count_direct_calls_named(mir, "rt_closure_get_capture")).to_equal(1)
```

</details>

#### lowers a capturing lambda returned from a fn

- lowers a capturing lambda returned from a fn
   - Expected: has_function_prefix(lower_source(src), "__lambda_lift_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a capturing lambda returned from a fn")
val src = "fn make_adder(k: i64) -> fn(i64) -> i64:\n    \\v: v + k\n"
val errs = errors_joined(lowering_errors(src))
expect_not(errs.contains("E-MIR-EXPR-Lambda"))
expect(has_function_prefix(lower_source(src), "__lambda_lift_")).to_equal(true)
```

</details>

#### lowers a nested capturing lambda (inner captures the outer's param and a local)

- lowers a nested capturing lambda (inner captures the outer's param and a local)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a nested capturing lambda (inner captures the outer's param and a local)")
val src = "fn apply(f: fn(i64) -> i64, x: i64) -> i64:\n    f(x)\nfn run() -> i64:\n    val outer = 2\n    val nested = \\a: apply(\\b: b + a + outer, 10)\n    nested(1)\n"
val errs = errors_joined(lowering_errors(src))
expect_not(errs.contains("undefined variable"))
expect_not(errs.contains("E-MIR-EXPR-Lambda"))
```

</details>

#### calls a fn-typed struct field holding a capturing lambda via method-call syntax

- calls a fn-typed struct field holding a capturing lambda via method-call syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("calls a fn-typed struct field holding a capturing lambda via method-call syntax")
val src = "struct Holder:\n    f: fn(i64) -> i64\nfn run() -> i64:\n    val k = 5\n    val h = Holder(f: \\v: v * k)\n    h.f(4)\n"
val errs = errors_joined(lowering_errors(src))
expect_not(errs.contains("unresolved method call: f"))
expect_not(errs.contains("E-MIR-EXPR-Lambda"))
```

</details>

### capturing lambdas native-build dual-run

#### native-builds all six capture shapes and matches the interpreter lane

- native-builds all six capture shapes and matches the interpreter lane
- Write the fixture and run it on the interpreter lane
   - Expected: interp.0 equals `EXPECTED`
- native-build the same source (one build for all shapes)
   - Expected: log.0 equals ``
- Run the native artifact: by-value capture, same output as interpreter
   - Expected: native.0 equals `EXPECTED + "RC=0\n"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("native-builds all six capture shapes and matches the interpreter lane")
step("Write the fixture and run it on the interpreter lane")
# An ABSOLUTE scratch dir: a repo-relative path under build/ is read by
# native-build as module `build.test_artifacts...` and fails with
# "missing importing module surface".
var scratch = env_get("SIMPLE_TEST_SCRATCH")
if scratch == "":
    scratch = "/tmp"
val dir = scratch + "/native_capturing_lambda_closure_conversion"
val src = dir + "/prog.spl"
val bin_out = dir + "/prog.bin"
process_run("sh", ["-c", "mkdir -p " + dir + " && rm -f " + bin_out])
file_write(src, PROGRAM_SOURCE)
# Newlines are stripped on BOTH lanes: native `print` drops its trailing
# newline (separate bug native_build_print_drops_newline_2026-08-17);
# this spec pins the closure VALUES, not that defect.
val interp = process_run("sh", ["-c", simple_bin() + " run " + src + " 2>/dev/null | tr -d '\\n'"])
expect(interp.0).to_equal(EXPECTED)

step("native-build the same source (one build for all shapes)")
val cmd = ("SIMPLE_TIMEOUT_SECONDS=0 nice -n 19 " + simple_bin() +
    " native-build --threads 8 -o " + bin_out + " " + src +
    " > " + dir + "/build.log 2>&1; echo RC=$?")
val build = process_run("sh", ["-c", cmd])
val log = process_run("sh", ["-c", "grep -h 'undefined variable\\|E-MIR-EXPR-Lambda\\|unresolved method call' " + dir + "/build.log | sort -u | head -3"])
expect(log.0).to_equal("")
expect(build.0).to_contain("RC=0")

step("Run the native artifact: by-value capture, same output as interpreter")
val native = process_run("sh", ["-c", bin_out + " 2>&1 | tr -d '\\n'; echo RC=$?"])
expect(native.0).to_equal(EXPECTED + "RC=0\n")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b569c55209ca3dd0ca00f1b64b069b655791ec60e89fee4bf9ec13cc5de05467`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b569c55209ca3dd0ca00f1b64b069b655791ec60e89fee4bf9ec13cc5de05467`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b569c55209ca3dd0ca00f1b64b069b655791ec60e89fee4bf9ec13cc5de05467`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a val-bound capturing lambda call without 'undefined variable'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes a capturing lambda call argument as an rt_closure_new env' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a capturing lambda returned from a fn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
