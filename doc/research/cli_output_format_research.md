# CLI Output Format Research: Test/Build/Lint Commands

**Date:** 2026-03-13
**Purpose:** Research how major toolchains handle compact CLI output for test, build, and lint commands. Focus on progress display, log saving, and compact vs verbose modes.

---

## 1. Rust / Cargo

### cargo build (default)

```
   Compiling serde v1.0.193
   Compiling tokio v1.35.0
   Compiling my-project v0.1.0 (/home/user/my-project)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 4.32s
```

- **Progress:** Each crate gets a `Compiling` line with green-colored verb
- **Verbs are right-aligned** and color-coded: `Compiling`, `Downloading`, `Finished`, `Running`, `warning`
- **No progress bar** in default cargo, just streaming `Compiling` lines
- **Warnings** appear inline between Compiling lines
- **Summary:** Single `Finished` line with profile, target info, and total time

### cargo build (verbose: -v)

Shows full compiler invocations (`rustc --crate-name ...`). With `-vv`, also shows build script output.

### cargo test (default)

```
   Compiling my-project v0.1.0 (/home/user/my-project)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 2.14s
     Running unittests src/lib.rs (target/debug/deps/my_project-abc123)

running 4 tests
test tests::test_add ... ok
test tests::test_subtract ... ok
test tests::test_multiply ... ok
test tests::test_divide ... FAILED

failures:

---- tests::test_divide stdout ----
thread 'tests::test_divide' panicked at src/lib.rs:42:9:
assertion `left == right` failed
  left: 3
 right: 4

failures:
    tests::test_divide

test result: FAILED. 3 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.02s
```

- **Progress:** One line per test: `test name ... ok/FAILED`
- **Errors:** Failed test stdout shown in `failures:` section
- **Summary:** `test result: OK/FAILED. N passed; N failed; N ignored; N measured; N filtered out`

### cargo test (quiet: -q / --format terse)

```
running 47 tests
...............................................
test result: ok. 47 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.31s
```

- **Progress:** Single dot `.` per passing test, `F` per failure
- **Summary:** Same summary line as default

### cargo clippy

```
    Checking my-project v0.1.0 (/home/user/my-project)
warning: redundant clone
  --> src/main.rs:15:14
   |
15 |     let s = name.clone();
   |                  ^^^^^^^^
   |
   = help: for further information visit https://rust-lang.github.io/rust-clippy/master/index.html#redundant_clone
   = note: `#[warn(clippy::redundant_clone)]` on by default

warning: `my-project` generated 1 warning
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.05s
```

- **Errors/warnings:** Shows file location, code snippet with arrows, help link
- **Summary:** `warning: \`crate\` generated N warning(s)`

### cargo-nextest (popular alternative test runner)

```
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.15s
------------
 Nextest run ID a1b2c3d4 with nextest profile: default
    Starting 14 tests across 3 binaries (177 tests skipped)
        PASS [   0.005s] my-crate test::unit::parse_config
        PASS [   0.004s] my-crate test::unit::validate_input
        PASS [   0.010s] my-crate test::integration::end_to_end
        FAIL [   0.011s] my-crate test::unit::edge_case
------------
     Summary [   0.015s] 14 tests run: 13 passed, 1 failed, 177 skipped
```

- **Progress options:** `bar` (default in terminal), `counter`, `only` (bar + hide successful output)
- **Progress bar** shows up to 8 currently-running tests
- **Non-interactive** falls back to counter mode
- **Status levels:** none < fail < retry < slow < pass < skip < all
- **Log saving:** JUnit XML output via `--reporter=junit`

---

## 2. Go

### go build (default)

```
$ go build ./...
$
```

- **Silent on success** -- produces NO output at all
- Only prints errors if compilation fails

### go build (-v verbose)

```
$ go build -v ./...
net/http
encoding/json
myproject/internal/parser
myproject/cmd/server
```

- Shows package names as they compile

### go test (default)

```
ok      myproject/pkg/parser    0.003s
ok      myproject/pkg/lexer     0.005s
ok      myproject/pkg/codegen   0.012s
```

- **Extremely compact:** One line per package: `ok  package  time`
- **Silent on pass** for individual tests -- only shows package-level summary
- Failures always show full output regardless of mode

### go test (failure)

```
--- FAIL: TestDivide (0.00s)
    math_test.go:15: expected 5, got 4
FAIL
FAIL    myproject/pkg/math   0.003s
```

### go test (-v verbose)

```
=== RUN   TestAdd
--- PASS: TestAdd (0.00s)
=== RUN   TestSubtract
--- PASS: TestSubtract (0.00s)
=== RUN   TestMultiply
--- PASS: TestMultiply (0.00s)
PASS
ok      myproject/pkg/math   0.003s
```

- Shows `=== RUN`, `--- PASS/FAIL` for each test
- Sub-tests indented: `=== RUN   TestAdd/positive`, `--- PASS: TestAdd/positive`

### go vet

```
$ go vet ./...
# myproject/pkg/parser
./parser.go:42:2: printf: Sprintf format %d has arg s of wrong type string
```

- **Silent on success**
- Shows `# package` header then `file:line:col: message`

**Key insight:** Go is the most minimal -- completely silent on success.

---

## 3. Zig

### zig build (default)

Zig uses a **multi-line progress bar** that overwrites itself using terminal escape codes:

```
[3/7] Compiling src/main.zig...
[4/7] Compiling src/parser.zig...
```

When complete, the progress lines are erased and replaced with the build summary:

```
Build Summary: 3/3 steps succeeded
install success
 └─ install hello success
     └─ zig build-exe hello Debug native success 881ms MaxRSS: 220M
```

- **Progress:** Counter `[N/total]` with current action, overwrites in-place
- **Tree view** on completion showing step hierarchy
- **MaxRSS** (peak memory) shown per step
- **No output on success** in some configurations (just returns to prompt)

### zig test (default)

```
1/3 test.expect addOne adds one...OK
2/3 test.slicing...OK
3/3 test.formatting...OK
All 3 tests passed.
```

- **Progress:** `N/total` counter before each test name
- **Each test on one line** with `...OK` or `...FAIL`
- **Summary:** `All N tests passed.` or `N passed; N skipped; N failed.`

### zig test (failure)

```
1/2 test.expect addOne adds one...OK
2/2 test.broken test...FAIL
test.broken test...
  src/lib.zig:15:5: error: expected 5, found 4
0 passed; 0 skipped; 1 failed.
```

### Zig Progress Protocol (ZIG_PROGRESS)

Zig invented an **inter-process progress protocol**:
- Parent creates a pipe, passes FD to child via `ZIG_PROGRESS=3`
- Child sends serialized progress data over the pipe
- Parent draws the progress bar for all children
- Designed as an open standard any tool can adopt
- Zero performance overhead measured

**Key insight:** Zig's progress bar is the most sophisticated -- it composes progress from parallel child processes into a single unified display, and erases itself when done.

---

## 4. Bun

### bun test (default)

```
bun test v1.0.0

test.test.ts:
✓ add [0.87ms]
✓ multiply [0.02ms]

math.test.ts:
✓ divide [0.54ms]
✓ subtract [0.01ms]

 4 pass
 0 fail
 4 expect() calls
Ran 4 tests across 2 files. [12.00ms]
```

- **Checkmarks:** `✓` for pass (green), `✗` for fail (red)
- **Timing per test** in brackets
- **Grouped by file**
- **Summary:** N pass, N fail, N expect() calls, N tests across N files, total time
- Notably compact -- no header/footer decorations

### bun test (failure)

```
test.test.ts:
✓ add [0.87ms]
✗ divide [0.54ms]

 1 pass
 1 fail
 4 expect() calls

 1) divide
      math.test.ts:15:5

      Expected: 5
      Received: 4
```

### bun test (dots reporter: --reporter=dots)

```
....
4 pass, 0 fail
```

- Even more compact -- just dots like pytest -q

### AI-friendly mode

When `CLAUDECODE=1` is set, Bun outputs even more compact results -- shows failures and summary but hides verbose passing test output. Designed to conserve LLM context windows.

**Key insight:** Bun is very compact by default, and has specific AI-agent-aware output modes.

---

## 5. pytest

### pytest (default)

```
========================== test session starts ===========================
platform linux -- Python 3.12.0, pytest-8.0.0, pluggy-1.4.0
rootdir: /home/user/project
collected 47 items

test_math.py ..............                                         [ 29%]
test_parser.py .....................                                 [ 74%]
test_codegen.py ............                                        [100%]

========================== 47 passed in 0.34s ============================
```

- **Header:** Platform, versions, rootdir
- **Progress:** Dots per test (`.` pass, `F` fail, `E` error, `s` skip, `x` xfail)
- **Percentage** shown at right edge: `[29%]`, `[74%]`, `[100%]`
- **Summary line** in `=` borders: `N passed in Ns`

### pytest (failure)

```
========================== test session starts ===========================
...
test_math.py .F.                                                    [ 29%]

================================ FAILURES ================================
______________________________ test_divide _______________________________

    def test_divide():
>       assert divide(10, 3) == 4
E       assert 3 == 4
E        +  where 3 = divide(10, 3)

test_math.py:15: AssertionError
======================== short test summary info =========================
FAILED test_math.py::test_divide - assert 3 == 4
==================== 1 failed, 46 passed in 0.35s =======================
```

- **`FAILURES` section** with full assertion diff
- **`short test summary info`** section with one-liner per failure
- Color-coded: green for pass borders, red for fail borders

### pytest (quiet: -q)

```
...............................................                    [100%]
47 passed in 0.34s
```

- Just dots + percentage + one-line summary

### pytest (verbose: -v)

```
test_math.py::test_add PASSED                                      [ 14%]
test_math.py::test_subtract PASSED                                 [ 28%]
test_math.py::test_multiply PASSED                                 [ 42%]
```

- Full test path + PASSED/FAILED + percentage

### Log saving

- **JUnit XML:** `pytest --junitxml=report.xml`
- **HTML:** `pytest --html=report.html` (via pytest-html plugin)
- **`-ra`** flag: show extra test summary info for all except passed (recommended default)
- Configuration: `addopts = ["-ra", "-q"]` in pytest.ini

**Key insight:** Pytest's percentage indicator `[100%]` at the right margin is excellent for knowing how far along you are. The `short test summary info` section is great for quick failure scanning.

---

## 6. Jest

### Jest (default)

```
 PASS  src/math.test.js
 PASS  src/parser.test.js

Test Suites:  2 passed, 2 total
Tests:        8 passed, 8 total
Snapshots:    0 total
Time:         1.234 s
Ran all test suites.
```

- **Per-file status:** `PASS` (green) or `FAIL` (red) prefix
- **Summary block:** Suites, Tests, Snapshots, Time -- each on its own line
- Uses ANSI terminal painting to update in-place

### Jest (verbose: --verbose)

```
 PASS  src/math.test.js
  Math operations
    ✓ should add numbers (3 ms)
    ✓ should subtract numbers (1 ms)
    ✓ should multiply numbers
  Edge cases
    ✓ should handle zero

Test Suites:  1 passed, 1 total
Tests:        4 passed, 4 total
Snapshots:    0 total
Time:         0.892 s, estimated 1 s
Ran all test suites.
```

- Shows `describe` block hierarchy with `✓` checkmarks
- Timing per test in parentheses (only if > 0ms)

### Jest (failure)

```
 FAIL  src/math.test.js
  ● Math operations › should divide

    expect(received).toBe(expected) // Object.is equality

    Expected: 4
    Received: 3

      13 |   test('should divide', () => {
    > 14 |     expect(divide(10, 3)).toBe(4);
         |                           ^
      15 |   });

      at Object.<anonymous> (src/math.test.js:14:27)

Test Suites:  1 failed, 1 total
Tests:        1 failed, 3 passed, 4 total
Snapshots:    0 total
Time:         0.934 s
Ran all test suites.
```

- **Code snippet** with arrow pointing to failed assertion
- **Diff display** for expected vs received
- Uses terminal cursor control to paint summary at bottom

### Jest (--silent)

Suppresses console.log output from tests, but still shows test results.

**Key insight:** Jest's summary block (Suites/Tests/Snapshots/Time) is very scannable. The in-place terminal painting gives a live feel.

---

## 7. Gradle

### gradle build (default)

```
> Task :compileJava
> Task :processResources NO-SOURCE
> Task :classes
> Task :jar

BUILD SUCCESSFUL in 2s
4 actionable tasks: 4 executed
```

- **Task-level progress:** Each task printed as `> Task :name`
- **Status tags:** `UP-TO-DATE`, `NO-SOURCE`, `FROM-CACHE`
- **Summary:** `BUILD SUCCESSFUL/FAILED in Ns` + actionable task count

### gradle test (default)

```
> Task :compileJava UP-TO-DATE
> Task :compileTestJava
> Task :test

BUILD SUCCESSFUL in 4s
6 actionable tasks: 2 executed, 4 up-to-date
```

- **Test output is HIDDEN by default** -- only shows task-level info
- **Full HTML report** always generated at `build/reports/tests/test/index.html`

### gradle test (with testLogging configured)

```
> Task :test

com.example.MathTest > testAdd PASSED
com.example.MathTest > testSubtract PASSED
com.example.MathTest > testDivide FAILED
    org.opentest4j.AssertionFailedError: expected: <4> but was: <3>
        at com.example.MathTest.testDivide(MathTest.java:15)

3 tests completed, 1 failed

> Task :test FAILED

BUILD FAILED in 3s
```

### gradle test (failure, default config)

```
> Task :test FAILED

FAILURE: Build failed with an exception.

* What went wrong:
Execution failed for task ':test'.
> There were failing tests. See the report at:
  file:///home/user/project/build/reports/tests/test/index.html

BUILD FAILED in 4s
```

### Build Scans (--scan)

```
BUILD SUCCESSFUL in 4s
6 actionable tasks: 2 executed, 4 up-to-date

Publishing build scan...
https://scans.gradle.com/s/abc123def456
```

- Uploads full build metadata to Gradle's online service
- Includes console output, test results, timing, dependencies
- URL printed at end of build

### Log/report locations

| What | Where |
|------|-------|
| Test HTML report | `build/reports/tests/test/index.html` |
| Test XML results | `build/test-results/test/*.xml` |
| Build profile | `build/reports/profile/` (with `--profile`) |
| Build scan | `https://scans.gradle.com/s/<id>` (with `--scan`) |

**Key insight:** Gradle's default is extremely terse for tests (just task names). The real information is in the HTML report. The `--scan` feature is unique -- a URL to a rich web dashboard.

---

## 8. Bazel

### bazel build (default)

```
INFO: Analyzed target //:myapp (15 packages loaded, 87 targets configured).
INFO: Found 1 target...
Target //:myapp up-to-date:
  bazel-bin/myapp
INFO: Elapsed time: 3.245s, Critical Path: 2.11s
INFO: 7 processes: 3 internal, 4 linux-sandbox.
INFO: Build completed successfully, 7 total actions
```

- **Progress:** In-place progress bar showing `[N / total]` actions completed
- During build: `[3 / 7] Compiling src/main.cc`
- **Summary:** Elapsed time, critical path, process counts, total actions
- Progress bar overwrites itself in terminal

### bazel build (progress during execution)

```
[0 / 7] actions running
[1 / 7] Compiling src/lexer.cc
[3 / 7] Compiling src/parser.cc; Compiling src/ast.cc
[5 / 7] Compiling src/codegen.cc
[7 / 7] Linking myapp
```

- Shows `[completed / total]` with current action names
- Multiple concurrent actions shown on one line
- Updates in-place

### bazel test (default: --test_output=summary)

```
INFO: Analyzed 3 targets (0 packages loaded, 0 targets configured).
INFO: Found 3 test targets...
Target //:math_test up-to-date:
  bazel-bin/math_test
INFO: Elapsed time: 2.134s, Critical Path: 1.52s
INFO: 4 processes: 1 internal, 3 linux-sandbox.
INFO: Build completed successfully, 4 total actions
//:math_test                                                          PASSED in 0.3s
//:parser_test                                                        PASSED in 0.5s
//:codegen_test                                                       PASSED in 1.2s

Executed 3 out of 3 tests: 3 tests pass.
```

- **Per-target status:** Target name + PASSED/FAILED + time
- **Summary:** `Executed N out of N tests: N tests pass.`

### bazel test (failure)

```
//:math_test                                                          FAILED in 0.3s
  /home/user/.cache/bazel/_bazel_user/.../testlogs/math_test/test.log

Executed 3 out of 3 tests: 2 tests pass, 1 fails.
```

- **Log file path** shown for failed tests
- User can `cat` the log file to see full output

### bazel test (--test_output=errors)

Shows stdout/stderr of failed tests inline in terminal output.

### bazel test (--test_output=streamed)

Streams test output in real-time (disables parallel test execution).

### Test log locations

```
bazel-testlogs/
  math_test/
    test.log          # stdout/stderr capture
    test.xml          # JUnit XML results
  parser_test/
    test.log
    test.xml
```

- **Symlink:** `bazel-testlogs` in workspace root points to actual output directory
- **Always saved:** Every test run saves logs regardless of terminal output mode
- **Full path:** `$(bazel info output_path)/execroot/<workspace>/bazel-out/<config>/testlogs/`

### --test_summary options

| Value | Behavior |
|-------|----------|
| `short` | (default) PASS/FAIL per target + log path for failures |
| `terse` | Only print info about failed tests |
| `detailed` | Show individual test case results within targets |
| `none` | No summary |

**Key insight:** Bazel's separation of terminal output from saved logs is the cleanest model. The `bazel-testlogs/` symlink makes log files easily accessible. The `[N / total]` action counter with in-place updates is smooth.

---

## Comparison Matrix

| Tool | Default Progress | Compact Mode | Verbose Mode | Log Saving | "Show Last Log" |
|------|-----------------|--------------|--------------|------------|-----------------|
| **cargo test** | Line per test | `-q` dots | Default is verbose | No built-in | No |
| **cargo nextest** | Progress bar + running tests | `--show-progress=counter` | Status levels | JUnit XML | No |
| **go test** | One line per package | Default is compact | `-v` per test | No built-in | No |
| **zig test** | `N/total` counter | Default is compact | No built-in | No built-in | No |
| **zig build** | In-place `[N/total]` bar | Default | No built-in | No built-in | No |
| **bun test** | Checkmarks per test | `--reporter=dots` | Default is verbose | JUnit XML | No |
| **pytest** | Dots + `[N%]` | `-q` dots only | `-v` full names | JUnit XML, HTML | No |
| **Jest** | `PASS/FAIL` per file | `--silent` | `--verbose` tree | JUnit XML | No |
| **Gradle** | Task names only | Default is compact | `testLogging` config | HTML report always | `build/reports/` |
| **Bazel** | `[N/total]` actions | `--test_summary=terse` | `--test_output=all` | **Always saves** test.log | `bazel-testlogs/` |

---

## Key Design Patterns

### Pattern 1: Dots/Characters (pytest, cargo -q, bun --dots)
```
...F..s...........                                              [100%]
47 passed, 1 failed, 1 skipped in 0.34s
```
- One character per test: `.` pass, `F` fail, `s` skip
- Best for: huge test suites, quick visual scan
- Weakness: no test name visible until failure section

### Pattern 2: Counter Progress (Zig, Bazel)
```
[14/27] Compiling src/parser.zig...
```
- Shows `[completed/total]` + current action
- Overwrites in-place (no scrolling)
- Best for: builds with many parallel steps
- **Zig's innovation:** erases progress when done, leaving clean output

### Pattern 3: Line Per Test (cargo, bun, nextest)
```
test tests::parse_expression ... ok
test tests::parse_statement  ... FAILED
```
- Each test gets a full line with name + status
- Best for: moderate test counts, easy to find specific test
- Weakness: noisy for 1000+ tests

### Pattern 4: Grouped by File (bun, Jest, pytest)
```
src/math.test.ts:
  ✓ add [0.87ms]
  ✓ multiply [0.02ms]
```
- File header, then indented test results
- Best for: understanding test organization

### Pattern 5: Silent Success (Go, Gradle)
```
ok  myproject/pkg/parser  0.003s
```
- Minimal or no output on success
- Verbose details only on failure
- Best for: fast feedback, trust-based workflows

### Pattern 6: Log File + Compact Terminal (Bazel, Gradle)
```
//:math_test    PASSED in 0.3s
//:parser_test  FAILED in 0.5s
  /path/to/bazel-testlogs/parser_test/test.log

Executed 2 out of 2 tests: 1 test passes, 1 fails.
```
- Compact summary on terminal
- Full logs always saved to known location
- **This is the most scalable pattern for large projects**

---

## Recommendations for Simple Language Compiler

Based on this research, the recommended approach combines the best patterns:

### Default Mode (compact)
1. **Counter progress** like Zig: `[3/47] test/lib/parser_spec.spl`
2. **Overwrite in-place** during execution
3. On completion, show **summary only:**
   ```
   47 passed, 0 failed, 2 skipped in 1.34s
   ```

### On Failure
4. Show **short failure summary** like pytest:
   ```
   FAILED test/lib/parser_spec.spl::parse_expression - expected 5, got 4
   FAILED test/lib/codegen_spec.spl::emit_call - undefined variable 'x'

   45 passed, 2 failed in 1.34s
   Full log: build/test-log/latest.log
   ```

### Log Saving (like Bazel/Gradle)
5. **Always save** full log to `build/test-log/latest.log`
6. Per-file logs at `build/test-log/<test-path>.log`
7. **`simple test --show-log`** to view last run's full output
8. **`simple test --show-log <test>`** to view specific test's output

### Verbose Mode
9. **`simple test -v`** shows line per test like cargo
10. **`simple test -vv`** shows full output including stdout capture

### Build Output
11. Like Zig: `[3/12] Compiling src/compiler/10.frontend/parser.spl`
12. Overwrite in-place, clean tree summary on completion:
    ```
    Build successful in 3.2s (12 files compiled, 0 warnings)
    ```

### Lint Output
13. Like cargo clippy -- show warnings inline with code context
14. Summary at end: `3 warnings, 0 errors`

---

## Sources

- [Cargo Test - The Cargo Book](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
- [Controlling How Tests Are Run - The Rust Programming Language](https://doc.rust-lang.org/book/ch11-02-running-tests.html)
- [cargo test output, --nocapture and --format (Issue #6110)](https://github.com/rust-lang/cargo/issues/6110)
- [Running tests - cargo-nextest](https://nexte.st/docs/running/)
- [Reporting test results - cargo-nextest](https://nexte.st/docs/reporting/)
- [Add a test - Go Documentation](https://go.dev/doc/tutorial/add-a-test)
- [Use the -v flag for verbose Go tests](https://alexwlchan.net/notes/2025/go-test-verbose/)
- [Zig's New CLI Progress Bar Explained - Andrew Kelley](https://andrewkelley.me/post/zig-new-cli-progress-bar-explained.html)
- [Zig Build System](https://ziglang.org/learn/build-system/)
- [Running Tests - zig.guide](https://zig.guide/getting-started/running-tests/)
- [Bun Test Runner](https://bun.com/docs/test)
- [Consider summarized test output for bun test (Issue #5437)](https://github.com/oven-sh/bun/issues/5437)
- [Managing pytest's output](https://docs.pytest.org/en/stable/how-to/output.html)
- [pytest Getting Started](https://docs.pytest.org/en/stable/getting-started.html)
- [Jest CLI Options](https://jestjs.io/docs/cli)
- [Provide a --simple-output option for Jest (Issue #2471)](https://github.com/jestjs/jest/issues/2471)
- [Gradle Build Scans](https://docs.gradle.org/current/userguide/inspect.html)
- [Gradle Testing in Java & JVM projects](https://docs.gradle.org/current/userguide/java_testing.html)
- [Gradle - How to display test result in console](https://mkyong.com/gradle/gradle-display-test-results-in-console/)
- [Bazel Commands and Options](https://bazel.build/docs/user-manual)
- [Bazel Test Outputs - Lei Mao's Log Book](https://leimao.github.io/blog/Bazel-Test-Outputs/)
- [Bazel Output Directory Layout](https://bazel.build/remote/output-directories)
- [Bazel Testing Tips - EngFlow Blog](https://blog.engflow.com/2023/09/18/bazel-testing-tips/)
