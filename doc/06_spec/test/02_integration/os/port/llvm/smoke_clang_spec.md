# Smoke Clang Specification

> _Env-gated checks for a working clang cross-toolchain targeting x86_64-simpleos._

<!-- sdn-diagram:id=smoke_clang_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smoke_clang_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smoke_clang_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smoke_clang_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Clang Specification

## Scenarios

### SimpleOS cross clang smoke
_Env-gated checks for a working clang cross-toolchain targeting x86_64-simpleos._

#### cross clang binary exists at $LLVM_BUILD/bin/clang

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = llvm_build()
if lb == "":
    return "skip: LLVM_BUILD not set"
val clang = "{lb}/bin/clang"
fs.exists(clang).to_equal(true)
```

</details>

#### reports x86_64-simpleos as the target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = llvm_build()
if lb == "":
    return "skip: LLVM_BUILD not set"
val clang = "{lb}/bin/clang"
val (out, err, code) = process.run(clang, ["--print-target-triple"])
code.to_equal(0)
out.trim().to_equal("x86_64-simpleos")
```

</details>

#### compiles hello.c to x86_64-simpleos .o with exit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = llvm_build()
if lb == "":
    return "skip: LLVM_BUILD not set"
val clang = "{lb}/bin/clang"
val (out, err, code) = process.run(clang, [
    "--target=x86_64-simpleos",
    "-c",
    HELLO_C,
    "-o",
    OUT_O,
])
code.to_equal(0)
fs.exists(OUT_O).to_equal(true)
```

</details>

#### llvm-nm on the .o shows 'main' symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = llvm_build()
if lb == "":
    return "skip: LLVM_BUILD not set"
val nm = "{lb}/bin/llvm-nm"
val (out, err, code) = process.run(nm, [OUT_O])
code.to_equal(0)
out.contains("main").to_equal(true)
```

</details>

#### links the object into a SimpleOS ELF when the sysroot is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = llvm_build()
if lb == "":
    return "skip: LLVM_BUILD not set"
val sysroot = sysroot_dir()
if not fs.exists("{sysroot}/share/simpleos/simpleos.ld"):
    return "skip: SimpleOS sysroot not built"
val lld = "{lb}/bin/ld.lld"
val (out, err, code) = process.run(lld, [
    "-T", "{sysroot}/share/simpleos/simpleos.ld",
    "{sysroot}/lib/crt0.o",
    OUT_O,
    "-L", "{sysroot}/lib",
    "-lsimpleos_c",
    "-o", OUT_ELF,
])
code.to_equal(0)
fs.exists(OUT_ELF).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/llvm/smoke_clang_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS cross clang smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
