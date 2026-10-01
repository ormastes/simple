# Core C Bootstrap Runtime Capsule Contract Specification

> Tests covering direct core-C bootstrap runtime capsule producer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Core C Bootstrap Runtime Capsule Contract Specification

## Scenarios

### direct core-C bootstrap runtime capsule producer

#### uses the canonical ordered core-C source graph

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the canonical ordered core-C source graph
   - Expected: source does not contain `runtime_https_openssl_core.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the canonical ordered core-C source graph")
val source = file_read(PRODUCER)
for input in [
    "runtime_native.c",
    "runtime_contracts.c",
    "runtime_framebuffer.c",
    "runtime_directx_core.c",
    "runtime_legacy_core.c",
    "runtime_fork.c",
    "runtime_memtrack.c",
    "runtime_process.c",
    "runtime_font.c",
    "runtime_pool.c",
    "runtime_simd_utf8.c",
    "runtime_simd_dispatch.c"
]:
    expect(source).to_contain(input)
expect(source).to_contain("hosted_cocoa.c")
expect(source).to_contain("hosted_win32.c")
expect(source).to_contain("platform/platform_macos.h")
expect(source).to_contain("platform/unix_common.h")
expect(source).to_contain("stb_truetype.h")
expect(source.contains("runtime_https_openssl_core.c")).to_equal(false)
```

</details>

#### builds a deterministic archive without a language compiler lane

- builds a deterministic archive without a language compiler lane
   - Expected: source does not contain `bin/" + "simple`
   - Expected: source does not contain `native-" + "build`
   - Expected: source does not contain `car" + "go`
   - Expected: source does not contain `SIMPLE_ALLOW_" + "FREESTANDING_STUBS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a deterministic archive without a language compiler lane")
val source = file_read(PRODUCER)
expect(source).to_contain("\"$CC_PATH\" $COMMON_FLAGS $TARGET_FLAGS")
expect(source).to_contain("\"$AR_PATH\" rcsD \"$ARCHIVE\"")
expect(source).to_contain("ZERO_AR_DATE=1 \"$AR_PATH\" rcs \"$ARCHIVE\"")
expect(source).to_contain("-MMD -MF \"$depfile\"")
expect(source).to_contain("for declared_input in $SOURCE_FILES $HEADER_FILES")
expect(source).to_contain("repeat-compile-failed")
expect(source).to_contain("repeat-build-archive-mismatch")
expect(source).to_contain("-DSIMPLE_CORE_C_STANDALONE=1")
expect(source).to_contain("-mno-outline-atomics")
expect(source.contains("bin/" + "simple")).to_equal(false)
expect(source.contains("native-" + "build")).to_equal(false)
expect(source.contains("car" + "go")).to_equal(false)
expect(source.contains("SIMPLE_ALLOW_" + "FREESTANDING_STUBS")).to_equal(false)
```

</details>

#### fails closed on dirty input and existing output

- fails closed on dirty input and existing output


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed on dirty input and existing output")
val source = file_read(PRODUCER)
expect(source).to_contain("jj -R \"$ROOT_DIR\" log -r @")
expect(source).to_contain("jj-runtime-tree-unavailable")
expect(source).to_contain("git status --porcelain --untracked-files=all")
expect(source).to_contain("runtime-source-dirty")
expect(source).to_contain("output-already-exists")
expect(source).to_contain("missing-runtime-input")
expect(source).to_contain("archive-empty")
```

</details>

#### requires the contract ABI from the dedicated runtime-contracts provider

- requires the contract ABI from the dedicated runtime-contracts provider
   - Expected: native does not contain `void {symbol}(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the contract ABI from the dedicated runtime-contracts provider")
val producer = file_read(PRODUCER)
val contracts = file_read("src/runtime/runtime_contracts.c")
val native = file_read("src/runtime/runtime_native.c")
val header = file_read("src/runtime/runtime.h")
for symbol in ["simple_contract_check", "simple_contract_check_msg"]:
    expect(contracts).to_contain("void {symbol}(")
    # Exactly one definition: runtime_native.c must not redefine it.
    expect(native.contains("void {symbol}(")).to_equal(false)
    expect(header).to_contain("void     {symbol}(")
    expect(producer).to_contain("{symbol}_archive_symbol=T")
    expect(producer).to_contain("{symbol}_provider=runtime_contracts.o")
```

</details>

#### reports how many checks it actually executed

- reports how many checks it actually executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports how many checks it actually executed")
val source = file_read(PRODUCER)
expect(source).to_contain("core_c_runtime_capsule_checks_executed=")
expect(source).to_contain("checks_executed=$CHECKS_RUN")
expect(source).to_contain("checks-executed-below-floor")
```

</details>

#### attests immutable inputs tools archive provider and self-check

- attests immutable inputs tools archive provider and self-check


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attests immutable inputs tools archive provider and self-check")
val source = file_read(PRODUCER)
for field in [
    "schema=core-c-bootstrap-runtime-capsule-v1",
    "head_revision=",
    "runtime_tree=",
    "cc_path=",
    "cc_binary_sha256=",
    "cc_version_sha256=",
    "ar_path=",
    "ar_binary_sha256=",
    "ar_version_sha256=",
    "nm_binary_sha256=",
    "nm_version_sha256=",
    "common_flags=",
    "target_flags=",
    "archive_mode=",
    "source_list_sha256=",
    "header_list_sha256=",
    "local_input_list_sha256=",
    "archive_sha256=",
    "repeat_archive_sha256=",
    "repeated_build_equal=true",
    "repeated_build_receipt_sha256=",
    "archive_members_sha256=",
    "producer_script_sha256="
]:
    expect(source).to_contain(field)
expect(source).to_contain("rt_string_free_archive_symbol=T")
expect(source).to_contain("rt_string_free_provider=runtime_native.o")
expect(source).to_contain("NF >= 3")
expect(source).to_contain("rt_string_free_selfcheck=pass")
expect(source).to_contain("rt_string_free_selfcheck.c")
expect(source).to_contain("SELFCHECK PASSED (0 failures)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering direct core-C bootstrap runtime capsule producer.
- direct core-C bootstrap runtime capsule producer

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

- Canonical SPipe generation for source `baf071501e147eafce5380a956821939a28c85a6a297ffd8bca31f9f6c714320`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `baf071501e147eafce5380a956821939a28c85a6a297ffd8bca31f9f6c714320`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `baf071501e147eafce5380a956821939a28c85a6a297ffd8bca31f9f6c714320`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl
mirror: doc/06_spec/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical ordered core-C source graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a deterministic archive without a language compiler lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on dirty input and existing output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
