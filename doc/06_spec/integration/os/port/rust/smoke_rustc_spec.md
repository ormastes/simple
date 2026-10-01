# Smoke Rustc Specification

> Tests covering SimpleOS Rust cross-compile smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Rustc Specification

## Scenarios

### SimpleOS Rust cross-compile smoke

#### target JSON exists at src/os/toolchain/rust/x86_64-unknown-simpleos.json

- target JSON exists at src/os/toolchain/rust/x86_64-unknown-simpleos.json
   - Expected: fs.file_exists(TARGET_JSON) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("target JSON exists at src/os/toolchain/rust/x86_64-unknown-simpleos.json")
"""Always passes when repo is intact — verifies the target spec file is present."""
expect(fs.file_exists(TARGET_JSON)).to_equal(true)
```

</details>

#### rustc --print target-list contains simpleos when using forked rustc

- rustc --print target-list contains simpleos when using forked rustc
   - Expected: res.exit_code equals `0`
   - Expected: res.stdout contains `simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rustc --print target-list contains simpleos when using forked rustc")
"""Skip when RUST_SRC is unset (system nightly does not know the custom target)."""
val rs = rust_src()
if rs == "":
    return "skip: RUST_SRC not set — forked rustc not configured"
val rustc = "{rs}/bin/rustc"
val res = process.run(rustc, ["--print", "target-list"])
expect(res.exit_code).to_equal(0)
expect(res.stdout.contains("simpleos")).to_equal(true)
```

</details>

#### cargo +nightly build --target x86_64-unknown-simpleos exits 0

- cargo +nightly build --target x86_64-unknown-simpleos exits 0
   - Expected: res.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cargo +nightly build --target x86_64-unknown-simpleos exits 0")
"""Skip when RUST_BUILD_DRY_RUN=1 or SIMPLEOS_SYSROOT is unset."""
if rust_gate() == false:
    return "skip: no RUST_SRC and no system nightly rustc"
val dry = rt_env_get("RUST_BUILD_DRY_RUN")
if dry == "1":
    return "skip: RUST_BUILD_DRY_RUN=1"
val sysroot = rt_env_get("SIMPLEOS_SYSROOT")
if sysroot == nil:
    return "skip: SIMPLEOS_SYSROOT not set"
if sysroot == "":
    return "skip: SIMPLEOS_SYSROOT not set"
val res = process.run("cargo", [
    "+nightly",
    "build",
    "--release",
    "--target",
    "../../src/os/toolchain/rust/x86_64-unknown-simpleos.json",
    "-Z",
    "build-std=core,alloc,compiler_builtins",
], HELLO_RS_DIR)
expect(res.exit_code).to_equal(0)
```

</details>

#### output binary exists after build

- output binary exists after build
   - Expected: fs.file_exists(HELLO_RS_OUT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("output binary exists after build")
"""Skip when RUST_BUILD_DRY_RUN=1 or SIMPLEOS_SYSROOT is unset."""
if rust_gate() == false:
    return "skip: no RUST_SRC and no system nightly rustc"
val dry = rt_env_get("RUST_BUILD_DRY_RUN")
if dry == "1":
    return "skip: RUST_BUILD_DRY_RUN=1"
val sysroot = rt_env_get("SIMPLEOS_SYSROOT")
if sysroot == nil:
    return "skip: SIMPLEOS_SYSROOT not set"
if sysroot == "":
    return "skip: SIMPLEOS_SYSROOT not set"
expect(fs.file_exists(HELLO_RS_OUT)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/os/port/rust/smoke_rustc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Rust cross-compile smoke.
- SimpleOS Rust cross-compile smoke

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `308047ad437c603471530b5b12cb7395669cee30737acb27c6f178efecd8d2c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `308047ad437c603471530b5b12cb7395669cee30737acb27c6f178efecd8d2c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `308047ad437c603471530b5b12cb7395669cee30737acb27c6f178efecd8d2c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/os/port/rust/smoke_rustc_spec.spl
mirror: doc/06_spec/integration/os/port/rust/smoke_rustc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/port/rust/smoke_rustc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/port/rust/smoke_rustc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/port/rust/smoke_rustc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/os/port/rust/smoke_rustc_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'target JSON exists at src/os/toolchain/rust/x86_64-unknown-simpleos.json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/rust/smoke_rustc_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rustc --print target-list contains simpleos when using forked rustc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/rust/smoke_rustc_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cargo +nightly build --target x86_64-unknown-simpleos exits 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
