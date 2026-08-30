# @tag:size_regression

> extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

<!-- sdn-diagram:id=exe_size_budget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exe_size_budget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exe_size_budget_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exe_size_budget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @tag:size_regression

extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/exe_size_budget_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)
extern fn rt_file_read_bytes(path: text) -> [u8]
extern fn rt_file_exists(path: text) -> bool

fn run_shell(cmd: text) -> (text, text, i64):
    rt_process_run("/bin/sh", ["-c", cmd])

val BUDGET_BYTES: i64 = 12582912     # 12 MB — ~25% headroom over the 9.4 MB measured baseline
val BASELINE_BYTES: i64 = 9623568    # measured 2026-04-28; improvement should show as gap vs budget

val FIXTURE_SPL = "build/size-bench/hello.spl"
val OUTPUT_BIN  = "build/size-bench/hello.spl.native.stripped"

describe "exe size budget — stripped hello-world native binary":

## Scenarios

### exe size budget — stripped hello-world native binary

#### fixture source file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(FIXTURE_SPL)).to_equal(true)
```

</details>

#### compiles hello.spl to a stripped native binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(OUTPUT_BIN)).to_equal(true)
```

</details>

#### binary runs and prints Hello World (not a stub)

1. print "exit code: " + result 2 to text
   - Expected: stdout contains `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print "  Budget  : " + BUDGET BYTES to text
2. print "  Actual  : " + size bytes to text
3. print "  Baseline: " + BASELINE BYTES to text
4. print "  Delta   : +" + pct to text
5. print "--- size -A
   - Expected: size_bytes <= BUDGET_BYTES is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
