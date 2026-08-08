# Smoke Clang Specification

> _Env-gated checks for a working clang cross-toolchain targeting x86_64-unknown-simpleos._

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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Clang Specification

## Scenarios

### SimpleOS cross clang smoke
_Env-gated checks for a working clang cross-toolchain targeting x86_64-unknown-simpleos._

#### cross clang binary exists at canonical build path

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if llvm_build_configured():
    check(regular_file_exists(llvm_tool("clang")))
```

</details>

#### reports x86_64-unknown-simpleos as the target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if llvm_build_configured() and !cross_clang_guest_only():
    val code = clang_probe()
    expect(code).to_equal(0)
    val triple = process.run("cat", [TRIPLE_TXT]).stdout.trim()
    expect(triple).to_equal("x86_64-unknown-simpleos")
```

</details>

#### compiles hello.c to x86_64-unknown-simpleos .o with exit 0

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cross_clang_host_runnable():
    val result = process.run(llvm_tool("clang"), [
        "--target=x86_64-unknown-simpleos",
        "-c",
        HELLO_C,
        "-o",
        OUT_O,
    ])
    expect(result.exit_code).to_equal(0)
    check(regular_file_exists(OUT_O))
```

</details>

#### llvm-nm on the .o shows 'main' symbol

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cross_clang_host_runnable():
    val result = process.run(llvm_tool("llvm-nm"), [OUT_O])
    expect(result.exit_code).to_equal(0)
    check(result.stdout.contains("main"))
```

</details>

#### links the object into a SimpleOS ELF when the sysroot is available

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cross_clang_host_runnable():
    val sysroot = sysroot_dir()
    if regular_file_exists("{sysroot}/share/simpleos/simpleos.ld"):
        expect(sysroot_target_triple()).to_equal("x86_64-unknown-simpleos")
        val stale = process.run("sh", ["-c", "printf stale > {OUT_ELF}"])
        expect(stale.exit_code).to_equal(0)
        val result = process.run(llvm_tool("ld.lld"), [
            "-T", "{sysroot}/share/simpleos/simpleos.ld",
            "{sysroot}/lib/crt0.o",
            OUT_O,
            "-L", "{sysroot}/lib",
            "-lsimpleos_c",
            "-o", OUT_ELF,
        ])
        expect(result.exit_code).to_equal(0)
        check(regular_file_exists(OUT_ELF))
```

</details>

#### driver compiles and links hello.c through canonical clang

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cross_clang_host_runnable():
    val sysroot = sysroot_dir()
    if regular_file_exists("{sysroot}/share/simpleos/simpleos.ld"):
        expect(sysroot_target_triple()).to_equal("x86_64-unknown-simpleos")
        val result = process.run(llvm_tool("clang"), [
            "--target=x86_64-unknown-simpleos",
            HELLO_C,
            "-o", DRIVER_ELF,
        ])
        expect(result.exit_code).to_equal(0)
        check(regular_file_exists(DRIVER_ELF))
```

</details>

#### driver links compiler-rt builtins from the staged resource dir

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cross_clang_host_runnable():
    val sysroot = sysroot_dir()
    if regular_file_exists("{sysroot}/share/simpleos/simpleos.ld"):
        expect(sysroot_target_triple()).to_equal("x86_64-unknown-simpleos")
        val source = "__int128 div128(__int128 a,__int128 b){return a/b;} int main(void){return (int)div128(((__int128)1<<80),3);}"
        val write = process.run("sh", ["-c", "printf '%s\n' '{source}' > {BUILTINS_C}"])
        expect(write.exit_code).to_equal(0)
        val result = process.run(llvm_tool("clang"), [
            "--target=x86_64-unknown-simpleos",
            BUILTINS_C,
            "-o", BUILTINS_ELF,
        ])
        expect(result.exit_code).to_equal(0)
        check(regular_file_exists(BUILTINS_ELF))
```

</details>

#### aarch64 stage 2 artifacts and seeded builtins are present when built

- check
- check
   - Expected: clang_file.exit_code equals `0`
   - Expected: lld_file.exit_code equals `0`
- check
- check
- check
   - Expected: builtins_file.exit_code equals `0`
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if regular_file_exists(aarch64_llvm_tool("clang-20")):
    check(regular_file_exists(aarch64_llvm_tool("clang")))
    check(regular_file_exists(aarch64_llvm_tool("lld")))
    val clang_file = process.run("file", [aarch64_llvm_tool("clang-20")])
    val lld_file = process.run("file", [aarch64_llvm_tool("lld")])
    expect(clang_file.exit_code).to_equal(0)
    expect(lld_file.exit_code).to_equal(0)
    check(clang_file.stdout.contains("ARM aarch64"))
    check(lld_file.stdout.contains("ARM aarch64"))

    val builtins = "{sysroot_dir()}/lib/libclang_rt.builtins-aarch64.a"
    check(regular_file_exists(builtins))
    val builtins_file = process.run("file", [builtins])
    expect(builtins_file.exit_code).to_equal(0)
    check(builtins_file.stdout.contains("current ar archive"))
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
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
