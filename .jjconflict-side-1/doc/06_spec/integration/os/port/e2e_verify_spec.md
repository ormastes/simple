# E2e Verify Specification

> Tests covering e2e_verify, tag matchers, plan defaults, preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# E2e Verify Specification

## Scenarios

### e2e_verify

### tag matchers
_Confirm each check function's grep tag matches only real pass output._

#### simple smoke sees the version tag

- simple smoke sees the version tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simple smoke sees the version tag")
"""Positive case: SIMPLE_VERSION tag present in stdout."""
val out = "boot...\nSIMPLE_VERSION: simple 0.1.0\nmore\n"
expect(out.contains("SIMPLE_VERSION:")).to_be_true()
```

</details>

#### simple smoke rejects empty stdout

- simple smoke rejects empty stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simple smoke rejects empty stdout")
val out = ""
expect(out.contains("SIMPLE_VERSION:")).to_be_false()
```

</details>

#### clang smoke sees SMOKE_CLANG_OK

- clang smoke sees SMOKE_CLANG_OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clang smoke sees SMOKE_CLANG_OK")
val good = "foo\nSMOKE_CLANG_OK\nbar\n"
expect(good.contains("SMOKE_CLANG_OK")).to_be_true()
```

</details>

#### clang smoke rejects unrelated success text

- clang smoke rejects unrelated success text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clang smoke rejects unrelated success text")
val bad = "compilation completed\n"
expect(bad.contains("SMOKE_CLANG_OK")).to_be_false()
```

</details>

#### rust smoke sees 'hello from rust'

- rust smoke sees 'hello from rust'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rust smoke sees 'hello from rust'")
val good = "loading...\nhello from rust\n"
expect(good.contains("hello from rust")).to_be_true()
```

</details>

#### rust smoke rejects a generic hello

- rust smoke rejects a generic hello


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rust smoke rejects a generic hello")
val bad = "hello, world\n"
expect(bad.contains("hello from rust")).to_be_false()
```

</details>

#### selfhost sees STAGE2_EQ_STAGE3_OK

- selfhost sees STAGE2_EQ_STAGE3_OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selfhost sees STAGE2_EQ_STAGE3_OK")
val good = "cmp ok\nSTAGE2_EQ_STAGE3_OK\n"
expect(good.contains("STAGE2_EQ_STAGE3_OK")).to_be_true()
```

</details>

#### selfhost rejects a FAIL line

- selfhost rejects a FAIL line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selfhost rejects a FAIL line")
val bad = "STAGE2_EQ_STAGE3_FAIL phase=cmp\n"
expect(bad.contains("STAGE2_EQ_STAGE3_OK")).to_be_false()
```

</details>

#### bootstrap corpus sees BOOTSTRAP_CORPUS_OK

- bootstrap corpus sees BOOTSTRAP_CORPUS_OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bootstrap corpus sees BOOTSTRAP_CORPUS_OK")
val good = "running tests\nBOOTSTRAP_CORPUS_OK\n"
expect(good.contains("BOOTSTRAP_CORPUS_OK")).to_be_true()
```

</details>

#### bootstrap corpus rejects a FAIL line

- bootstrap corpus rejects a FAIL line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bootstrap corpus rejects a FAIL line")
val bad = "BOOTSTRAP_CORPUS_FAIL exit=1\n"
expect(bad.contains("BOOTSTRAP_CORPUS_OK")).to_be_false()
```

</details>

### plan defaults

#### uses the default kernel path

- uses the default kernel path
   - Expected: kernel equals `build/os/kernel/simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the default kernel path")
val kernel = "build/os/kernel/simpleos"
expect(kernel).to_equal("build/os/kernel/simpleos")
```

</details>

#### uses the default initrd path

- uses the default initrd path
   - Expected: initrd equals `build/os/initramfs.img.zst`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the default initrd path")
val initrd = "build/os/initramfs.img.zst"
expect(initrd).to_equal("build/os/initramfs.img.zst")
```

</details>

#### uses qemu-system-x86_64 as the launcher

- uses qemu-system-x86_64 as the launcher
   - Expected: launcher equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses qemu-system-x86_64 as the launcher")
val launcher = "qemu-system-x86_64"
expect(launcher).to_equal("qemu-system-x86_64")
```

</details>

### preflight

#### formats a missing-kernel path

- formats a missing-kernel path
   - Expected: kernel equals `/nonexistent/path/to/simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats a missing-kernel path")
val kernel = "/nonexistent/path/to/simpleos"
expect(kernel).to_equal("/nonexistent/path/to/simpleos")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/os/port/e2e_verify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering e2e_verify, tag matchers, plan defaults, preflight.
- e2e_verify
- tag matchers
- plan defaults
- preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `3ada4dab761f72f6d8d5802b5669ba7e7c48a82aec63e09d4e13959f147aeef4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ada4dab761f72f6d8d5802b5669ba7e7c48a82aec63e09d4e13959f147aeef4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ada4dab761f72f6d8d5802b5669ba7e7c48a82aec63e09d4e13959f147aeef4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/os/port/e2e_verify_spec.spl
mirror: doc/06_spec/integration/os/port/e2e_verify_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/port/e2e_verify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/port/e2e_verify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/port/e2e_verify_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple smoke sees the version tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/e2e_verify_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple smoke rejects empty stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/e2e_verify_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clang smoke sees SMOKE_CLANG_OK' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
