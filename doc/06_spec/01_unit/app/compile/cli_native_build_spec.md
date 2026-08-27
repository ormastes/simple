# Cli Native Build Specification

> Tests covering cli_native_build parser hardening.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Native Build Specification

## Scenarios

### cli_native_build parser hardening

#### accepts sole help and rejects malformed help combinations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts sole help and rejects malformed help combinations
   - Expected: cli_native_build(["native-build", "--help"]) equals `0`
   - Expected: cli_native_build(["native-build", "-h"]) equals `0`
   - Expected: cli_native_build(["native-build", "--entry-clousre", "--help"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts sole help and rejects malformed help combinations")
expect(cli_native_build(["native-build", "--help"])).to_equal(0)
expect(cli_native_build(["native-build", "-h"])).to_equal(0)
expect(cli_native_build(["native-build", "--entry-clousre", "--help"])).to_equal(2)
```

</details>

#### rejects unknown and incomplete options before compilation

- rejects unknown and incomplete options before compilation
   - Expected: cli_native_build_option_error(["native-build", "--entry-clousre"]) equals `unknown option: --entry-clousre`
   - Expected: cli_native_build_option_error(["native-build", "--entry", "--output", "tool"]) equals `--entry requires a value`
   - Expected: cli_native_build_option_error(["native-build", "--threads=-1"]) equals `--threads requires a positive integer`
   - Expected: cli_native_build_option_error(["native-build", "--timeout", "-1"]) equals `--timeout requires a positive integer`
   - Expected: cli_native_build_option_error(["native-build", "--timeout", "+1"]) equals `--timeout requires a positive integer`
   - Expected: cli_native_build_option_error(["native-build", "--timeout", "nope"]) equals `--timeout requires a positive integer`
   - Expected: cli_native_build_option_error(["native-build", "--jobs=0"]) equals `--jobs requires a positive integer`
   - Expected: cli_native_build_option_error(["native-build", "--output="]) equals `--output requires a value`
   - Expected: cli_native_build_option_error(["native-build", "--entry="]) equals `--entry requires a value`
   - Expected: cli_native_build_option_error(["native-build", "--jobs", "1", "--threads=2", "--strip", "--no-mangle"]) equals ``
   - Expected: cli_native_build_option_error(["native-build", "--low-memory"]) equals ``
   - Expected: cli_native_build_option_error(["native-build", "--timeout", "1", "--runtime-bundle", "auto", "--entry", "missing-entry.spl"]) equals ``
   - Expected: cli_native_build_option_error(["native-build", "--linker-script", "legacy.ld", "--runtime-path", "legacy-runtime", "--emit-archive", "--no-incremental", "--entry", "missing-entry.spl"]) equals ``
   - Expected: cli_native_build_option_error(["native-build", "--emit-shared", "--no-mangle", "--entry", "provider.spl"]) equals ``
   - Expected: cli_native_build(["native-build", "--entry", "missing-entry.spl", "--entry-clousre"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unknown and incomplete options before compilation")
expect(cli_native_build_option_error(["native-build", "--entry-clousre"])).to_equal("unknown option: --entry-clousre")
expect(cli_native_build_option_error(["native-build", "--entry", "--output", "tool"])).to_equal("--entry requires a value")
expect(cli_native_build_option_error(["native-build", "--threads=-1"])).to_equal("--threads requires a positive integer")
expect(cli_native_build_option_error(["native-build", "--timeout", "-1"])).to_equal("--timeout requires a positive integer")
expect(cli_native_build_option_error(["native-build", "--timeout", "+1"])).to_equal("--timeout requires a positive integer")
expect(cli_native_build_option_error(["native-build", "--timeout", "nope"])).to_equal("--timeout requires a positive integer")
expect(cli_native_build_option_error(["native-build", "--jobs=0"])).to_equal("--jobs requires a positive integer")
expect(cli_native_build_option_error(["native-build", "--output="])).to_equal("--output requires a value")
expect(cli_native_build_option_error(["native-build", "--entry="])).to_equal("--entry requires a value")
expect(cli_native_build_option_error(["native-build", "--jobs", "1", "--threads=2", "--strip", "--no-mangle"])).to_equal("")
expect(cli_native_build_option_error(["native-build", "--low-memory"])).to_equal("")
expect(cli_native_build_option_error(["native-build", "--timeout", "1", "--runtime-bundle", "auto", "--entry", "missing-entry.spl"])).to_equal("")
expect(cli_native_build_option_error(["native-build", "--linker-script", "legacy.ld", "--runtime-path", "legacy-runtime", "--emit-archive", "--no-incremental", "--entry", "missing-entry.spl"])).to_equal("")
expect(cli_native_build_option_error(["native-build", "--emit-shared", "--no-mangle", "--entry", "provider.spl"])).to_equal("")
expect(cli_native_build(["native-build", "--entry", "missing-entry.spl", "--entry-clousre"])).to_equal(2)
```

</details>

#### leaves an existing output untouched for invalid CLI

- leaves an existing output untouched for invalid CLI
   - Expected: file_write(output, "known-good") is true
   - Expected: cli_native_build(["native-build", "--entry", "missing-entry.spl", "--output", output, "--entry-clousre"]) equals `2`
   - Expected: file_read(output) equals `known-good`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves an existing output untouched for invalid CLI")
val output = "/tmp/simple_native_build_invalid_option_output"
expect(file_write(output, "known-good")).to_equal(true)
expect(cli_native_build(["native-build", "--entry", "missing-entry.spl", "--output", output, "--entry-clousre"])).to_equal(2)
expect(file_read(output)).to_equal("known-good")
file_delete(output)
```

</details>

#### rejects a trailing bare --log flag

- rejects a trailing bare --log flag
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a trailing bare --log flag")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log"])).to_equal(2)
```

</details>

#### rejects an empty inline --log value

- rejects an empty inline --log value
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log="]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects an empty inline --log value")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log="])).to_equal(2)
```

</details>

#### rejects bare --log followed by another option

- rejects bare --log followed by another option
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects bare --log followed by another option")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log", "--backend=llvm-lib"])).to_equal(2)
```

</details>

#### rejects typoed --log-prefixed flags

- rejects typoed --log-prefixed flags
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects typoed --log-prefixed flags")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--logg", "off"])).to_equal(2)
```

</details>

#### rejects a single invalid inline --log value

- rejects a single invalid inline --log value
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a single invalid inline --log value")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=maybe"])).to_equal(2)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

- rejects an invalid later --log value instead of keeping an earlier valid one
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects an invalid later --log value instead of keeping an earlier valid one")
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=on", "--log", "maybe"])).to_equal(2)
```

</details>

#### accepts a valid llvm-lib --log flag and forwards it before later build failure

- accepts a valid llvm-lib --log flag and forwards it before later build failure
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--log=off", "--entry", "missing-entry.spl"]) equals `1`
   - Expected: env_get("SIMPLE_OS_LOG_MODE") ?? "" equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts a valid llvm-lib --log flag and forwards it before later build failure")
val prior = env_get("SIMPLE_OS_LOG_MODE")
val before = if prior == nil: "" else: prior
expect(cli_native_build(["native-build", "--backend=llvm-lib", "--log=off", "--entry", "missing-entry.spl"])).to_equal(1)
expect(env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(before)
```

</details>

#### forwards an explicit runtime path to both native runtime lanes

- forwards an explicit runtime path to both native runtime lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("forwards an explicit runtime path to both native runtime lanes")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("var runtime_path = \"\"")
expect(source).to_contain("runtime_path = args[j]")
expect(source).to_contain("runtime_path = a.substring(15)")
expect(source).to_contain("env_set(\"SIMPLE_RUNTIME_PATH\", runtime_path)")
expect(source).to_contain("env_set(\"SIMPLE_CORE_RUNTIME_PATH\", runtime_path)")
```

</details>

#### propagates low-memory mode into both compiler driver branches

- propagates low-memory mode into both compiler driver branches
   - Expected: source.count("options.low_memory = low_memory") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("propagates low-memory mode into both compiler driver branches")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")

expect(source).to_contain("elif a == \"--low-memory\":")
expect(source).to_contain("var low_memory = false")
expect(source.count("options.low_memory = low_memory")).to_equal(2)
```

</details>

#### restores native runtime lanes after a failed build

- restores native runtime lanes after a failed build
   - Expected: env_set("SIMPLE_RUNTIME_PATH", "runtime-sentinel") is true
   - Expected: env_set("SIMPLE_CORE_RUNTIME_PATH", "core-runtime-sentinel") is true
   - Expected: cli_native_build(["native-build", "--backend=llvm-lib", "--runtime-path", "temporary-runtime", "--entry", "missing-entry.spl"]) equals `1`
   - Expected: env_get("SIMPLE_RUNTIME_PATH") ?? "" equals `runtime-sentinel`
   - Expected: env_get("SIMPLE_CORE_RUNTIME_PATH") ?? "" equals `core-runtime-sentinel`
   - Expected: env_set("SIMPLE_RUNTIME_PATH", prior_runtime) is true
   - Expected: env_set("SIMPLE_CORE_RUNTIME_PATH", prior_core_runtime) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("restores native runtime lanes after a failed build")
val prior_runtime = env_get("SIMPLE_RUNTIME_PATH") ?? ""
val prior_core_runtime = env_get("SIMPLE_CORE_RUNTIME_PATH") ?? ""
expect(env_set("SIMPLE_RUNTIME_PATH", "runtime-sentinel")).to_equal(true)
expect(env_set("SIMPLE_CORE_RUNTIME_PATH", "core-runtime-sentinel")).to_equal(true)

expect(cli_native_build(["native-build", "--backend=llvm-lib", "--runtime-path", "temporary-runtime", "--entry", "missing-entry.spl"])).to_equal(1)

expect(env_get("SIMPLE_RUNTIME_PATH") ?? "").to_equal("runtime-sentinel")
expect(env_get("SIMPLE_CORE_RUNTIME_PATH") ?? "").to_equal("core-runtime-sentinel")
expect(env_set("SIMPLE_RUNTIME_PATH", prior_runtime)).to_equal(true)
expect(env_set("SIMPLE_CORE_RUNTIME_PATH", prior_core_runtime)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compile/cli_native_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cli_native_build parser hardening.
- cli_native_build parser hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `173eede22163984b707a5f2d7f42a34b409f7c7864f34acce2d78206a2541e4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `173eede22163984b707a5f2d7f42a34b409f7c7864f34acce2d78206a2541e4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `173eede22163984b707a5f2d7f42a34b409f7c7864f34acce2d78206a2541e4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/compile/cli_native_build_spec.spl
mirror: doc/06_spec/01_unit/app/compile/cli_native_build_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/compile/cli_native_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/compile/cli_native_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/compile/cli_native_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/compile/cli_native_build_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts sole help and rejects malformed help combinations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/compile/cli_native_build_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown and incomplete options before compilation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/compile/cli_native_build_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves an existing output untouched for invalid CLI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
