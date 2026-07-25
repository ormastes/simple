# E2e Verify Specification

> _End-to-end verification orchestrator spec._

<!-- sdn-diagram:id=e2e_verify_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=e2e_verify_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

e2e_verify_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=e2e_verify_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# E2e Verify Specification

## Scenarios

### e2e_verify
_End-to-end verification orchestrator spec._

### tag matchers
_Confirm each check function's grep tag matches only real pass output._

#### simple smoke sees the version tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = "boot...\nSIMPLE_VERSION: simple 0.1.0\nmore\n"
expect(out.contains("SIMPLE_VERSION:")).to_be_true()
```

</details>

#### simple smoke rejects empty stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = ""
expect(out.contains("SIMPLE_VERSION:")).to_be_false()
```

</details>

#### clang smoke sees SMOKE_CLANG_OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "foo\nSMOKE_CLANG_OK\nbar\n"
expect(good.contains("SMOKE_CLANG_OK")).to_be_true()
```

</details>

#### clang smoke rejects unrelated success text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "compilation completed\n"
expect(bad.contains("SMOKE_CLANG_OK")).to_be_false()
```

</details>

#### rust smoke sees 'hello from rust'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "loading...\nhello from rust\n"
expect(good.contains("hello from rust")).to_be_true()
```

</details>

#### rust smoke rejects a generic hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "hello, world\n"
expect(bad.contains("hello from rust")).to_be_false()
```

</details>

#### selfhost sees STAGE2_EQ_STAGE3_OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "cmp ok\nSTAGE2_EQ_STAGE3_OK\n"
expect(good.contains("STAGE2_EQ_STAGE3_OK")).to_be_true()
```

</details>

#### selfhost rejects a FAIL line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "STAGE2_EQ_STAGE3_FAIL phase=cmp\n"
expect(bad.contains("STAGE2_EQ_STAGE3_OK")).to_be_false()
```

</details>

#### bootstrap corpus sees BOOTSTRAP_CORPUS_OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = "running tests\nBOOTSTRAP_CORPUS_OK\n"
expect(good.contains("BOOTSTRAP_CORPUS_OK")).to_be_true()
```

</details>

#### bootstrap corpus rejects a FAIL line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "BOOTSTRAP_CORPUS_FAIL exit=1\n"
expect(bad.contains("BOOTSTRAP_CORPUS_OK")).to_be_false()
```

</details>

### plan defaults

#### uses the default kernel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel = "build/os/kernel/simpleos"
expect(kernel).to_equal("build/os/kernel/simpleos")
```

</details>

#### uses the default initrd path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initrd = "build/os/initramfs.img.zst"
expect(initrd).to_equal("build/os/initramfs.img.zst")
```

</details>

#### uses qemu-system-x86_64 as the launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launcher = "qemu-system-x86_64"
expect(launcher).to_equal("qemu-system-x86_64")
```

</details>

### preflight

#### formats a missing-kernel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel = "/nonexistent/path/to/simpleos"
expect(kernel).to_equal("/nonexistent/path/to/simpleos")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/e2e_verify_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
