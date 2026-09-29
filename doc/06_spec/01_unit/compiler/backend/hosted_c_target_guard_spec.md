# Hosted C Target Guard Specification

> Tests covering hosted C target guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted C Target Guard Specification

## Scenarios

### hosted C target guard

#### allows implicit and explicit host targets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows implicit and explicit host targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows implicit and explicit host targets")
expect(hosted_c_target_matches_host("", "linux", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("host", "windows", "aarch64")).to_be(true)
expect(hosted_c_target_matches_host("native", "freebsd", "x86_64")).to_be(true)
```

</details>

#### allows same-host architecture aliases

- allows same-host architecture aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows same-host architecture aliases")
expect(hosted_c_target_matches_host("x86_64", "macos", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("x64", "windows", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("arm64", "windows", "aarch64")).to_be(true)
expect(hosted_c_target_matches_host("rv64", "linux", "riscv64")).to_be(true)
val x64_plan = hosted_c_compiler_plan("x64", "windows", "x86_64")
expect(x64_plan.supported).to_be(true)
expect(x64_plan.requires_cross).to_be(false)
```

</details>

#### allows matching Linux architectures

- allows matching Linux architectures


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows matching Linux architectures")
expect(hosted_c_target_matches_host("x86_64-unknown-linux-gnu", "linux", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("aarch64-unknown-linux-gnu", "linux", "aarch64")).to_be(true)
expect(hosted_c_target_matches_host("riscv64-unknown-linux-gnu", "linux", "riscv64")).to_be(true)
expect(hosted_c_target_matches_host("riscv64gc-unknown-linux-gnu", "linux", "riscv64")).to_be(true)
```

</details>

#### allows matching macOS Windows and FreeBSD targets

- allows matching macOS Windows and FreeBSD targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows matching macOS Windows and FreeBSD targets")
expect(hosted_c_target_matches_host("x86_64-apple-darwin", "macos", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("aarch64-apple-darwin", "macos", "aarch64")).to_be(true)
expect(hosted_c_target_matches_host("arm64-apple-darwin", "macos", "aarch64")).to_be(true)
expect(hosted_c_target_matches_host("x86_64-pc-windows-msvc", "windows", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("x64-pc-windows-msvc", "windows", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("x86_64-unknown-freebsd", "freebsd", "x86_64")).to_be(true)
expect(hosted_c_target_matches_host("aarch64-unknown-freebsd", "freebsd", "aarch64")).to_be(true)
```

</details>

#### keeps every supported native compiler plan out of the cross-capsule guard

- keeps every supported native compiler plan out of the cross-capsule guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every supported native compiler plan out of the cross-capsule guard")
val plans = [
    hosted_c_compiler_plan("x86_64-unknown-linux-gnu", "linux", "x86_64"),
    hosted_c_compiler_plan("aarch64-unknown-linux-gnu", "linux", "aarch64"),
    hosted_c_compiler_plan("riscv64-unknown-linux-gnu", "linux", "riscv64"),
    hosted_c_compiler_plan("x86_64-apple-darwin", "macos", "x86_64"),
    hosted_c_compiler_plan("aarch64-apple-darwin", "macos", "aarch64"),
    hosted_c_compiler_plan("x86_64-pc-windows-msvc", "windows", "x86_64"),
    hosted_c_compiler_plan("x86_64-unknown-freebsd", "freebsd", "x86_64"),
    hosted_c_compiler_plan("aarch64-unknown-freebsd", "freebsd", "aarch64")
]
for plan in plans:
    expect(plan.supported).to_be(true)
    expect(plan.requires_cross).to_be(false)
```

</details>

#### admits only hosted architectures with implemented linker and CRT ownership

- admits only hosted architectures with implemented linker and CRT ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits only hosted architectures with implemented linker and CRT ownership")
expect(hosted_native_link_arch_supported("linux", "x86_64")).to_be(true)
expect(hosted_native_link_arch_supported("linux", "aarch64")).to_be(true)
expect(hosted_native_link_arch_supported("linux", "riscv64")).to_be(true)
expect(hosted_native_link_arch_supported("linux", "rv64gc")).to_be(false)
expect(hosted_native_link_arch_supported("linux", "armv7")).to_be(false)
expect(hosted_native_link_arch_supported("windows", "x86_64")).to_be(true)
expect(hosted_native_link_arch_supported("windows", "i686")).to_be(false)
expect(hosted_native_link_arch_supported("windows", "aarch64")).to_be(false)
expect(hosted_native_link_arch_supported("windows", "arm64")).to_be(false)
expect(hosted_native_link_arch_supported("macos", "x86_64")).to_be(true)
expect(hosted_native_link_arch_supported("macos", "aarch64")).to_be(true)
expect(hosted_native_link_arch_supported("macos", "armv7l")).to_be(false)
expect(hosted_native_link_arch_supported("macos", "riscv64")).to_be(false)
expect(hosted_native_link_arch_supported("freebsd", "x86_64")).to_be(true)
expect(hosted_native_link_arch_supported("freebsd", "aarch64")).to_be(true)
expect(hosted_native_link_arch_supported("freebsd", "arm")).to_be(false)
expect(hosted_native_link_arch_supported("freebsd", "armv7")).to_be(false)
expect(hosted_native_link_arch_supported("freebsd", "armv7l")).to_be(false)
expect(hosted_native_link_arch_supported("freebsd", "riscv64")).to_be(false)
```

</details>

#### uses exact native x86_64 descriptors for each supported desktop OS

- uses exact native x86_64 descriptors for each supported desktop OS
   - Expected: freebsd.triple equals `x86_64-unknown-freebsd`
   - Expected: freebsd.linker equals `ld`
   - Expected: freebsd.crt_dir equals `/usr/lib`
   - Expected: freebsd.install_hint equals `FreeBSD base system toolchain`
   - Expected: windows.triple equals `x86_64-pc-windows-msvc`
   - Expected: windows.linker equals `link.exe`
   - Expected: macos.triple equals `x86_64-apple-darwin`
   - Expected: macos.linker_flavor equals `macho`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses exact native x86_64 descriptors for each supported desktop OS")
val freebsd = toolchain_x86_64_native("freebsd")
expect(freebsd.triple).to_equal("x86_64-unknown-freebsd")
expect(freebsd.linker).to_equal("ld")
expect(freebsd.crt_dir).to_equal("/usr/lib")
expect(freebsd.install_hint).to_equal("FreeBSD base system toolchain")

val windows = toolchain_x86_64_native("windows")
expect(windows.triple).to_equal("x86_64-pc-windows-msvc")
expect(windows.linker).to_equal("link.exe")
expect(windows.default_flags.contains("/MACHINE:X64")).to_be(true)

val macos = toolchain_x86_64_native("macos")
expect(macos.triple).to_equal("x86_64-apple-darwin")
expect(macos.linker_flavor).to_equal("macho")
expect(macos.default_flags.contains("-arch")).to_be(true)
```

</details>

#### uses native AArch64 descriptors only on supported hosts

- uses native AArch64 descriptors only on supported hosts
   - Expected: freebsd.triple equals `aarch64-unknown-freebsd`
   - Expected: freebsd.linker equals `ld`
   - Expected: freebsd.linker_flavor equals `gnu`
   - Expected: freebsd.crt_dir equals `/usr/lib`
   - Expected: freebsd.install_hint equals `FreeBSD base system toolchain`
   - Expected: freebsd_cross.target equals `CodegenTarget.AArch64`
   - Expected: freebsd_cross.triple equals `aarch64-unknown-freebsd`
   - Expected: freebsd_cross.linker equals ``
   - Expected: freebsd_cross.linker_flavor equals `unsupported`
   - Expected: freebsd_cross.sysroot equals ``
   - Expected: freebsd_cross.crt_dir equals ``
   - Expected: freebsd_cross.default_flags.len() equals `0`
   - Expected: macos.triple equals `aarch64-apple-darwin`
   - Expected: macos.linker_flavor equals `macho`
   - Expected: windows.triple equals `aarch64-pc-windows-msvc`
   - Expected: windows.linker equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses native AArch64 descriptors only on supported hosts")
val freebsd = toolchain_aarch64("freebsd", "aarch64")
expect(freebsd.triple).to_equal("aarch64-unknown-freebsd")
expect(freebsd.linker).to_equal("ld")
expect(freebsd.linker_flavor).to_equal("gnu")
expect(freebsd.crt_dir).to_equal("/usr/lib")
expect(freebsd.requires_external).to_be(false)
expect(freebsd.install_hint).to_equal("FreeBSD base system toolchain")

val freebsd_cross = toolchain_aarch64("freebsd", "x86_64")
expect(freebsd_cross.target).to_equal(CodegenTarget.AArch64)
expect(freebsd_cross.triple).to_equal("aarch64-unknown-freebsd")
expect(freebsd_cross.linker).to_equal("")
expect(freebsd_cross.linker_flavor).to_equal("unsupported")
expect(freebsd_cross.sysroot).to_equal("")
expect(freebsd_cross.crt_dir).to_equal("")
expect(freebsd_cross.default_flags.len()).to_equal(0)
expect(freebsd_cross.requires_external).to_be(true)
expect(freebsd_cross.is_available()).to_be(false)
expect(freebsd_cross.install_hint).to_contain("cross-linking is unsupported")

val macos = toolchain_aarch64("macos", "aarch64")
expect(macos.triple).to_equal("aarch64-apple-darwin")
expect(macos.linker_flavor).to_equal("macho")
expect(macos.default_flags.contains("arm64")).to_be(true)

val windows = toolchain_aarch64("windows", "aarch64")
expect(windows.triple).to_equal("aarch64-pc-windows-msvc")
expect(windows.linker).to_equal("")
expect(windows.requires_external).to_be(true)
expect(windows.is_available()).to_be(false)
expect(windows.install_hint).to_contain("unsupported")
```

</details>

#### fails every hosted ARMv7 descriptor closed

- fails every hosted ARMv7 descriptor closed
   - Expected: linux.linker equals ``
   - Expected: macos.linker equals ``
   - Expected: windows.linker equals ``
   - Expected: freebsd.linker equals ``
   - Expected: linux.triple equals `armv7-unknown-linux-gnueabihf`
   - Expected: macos.triple equals `armv7-apple-darwin`
   - Expected: windows.triple equals `armv7-pc-windows-msvc`
   - Expected: freebsd.triple equals `armv7-unknown-freebsd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails every hosted ARMv7 descriptor closed")
val linux = toolchain_armv7("linux", "armv7")
val macos = toolchain_armv7("macos", "armv7l")
val windows = toolchain_armv7("windows", "arm")
val freebsd = toolchain_armv7("freebsd", "armv7")
expect(linux.linker).to_equal("")
expect(macos.linker).to_equal("")
expect(windows.linker).to_equal("")
expect(freebsd.linker).to_equal("")
expect(linux.triple).to_equal("armv7-unknown-linux-gnueabihf")
expect(macos.triple).to_equal("armv7-apple-darwin")
expect(windows.triple).to_equal("armv7-pc-windows-msvc")
expect(freebsd.triple).to_equal("armv7-unknown-freebsd")
expect(linux.is_available()).to_be(false)
expect(macos.is_available()).to_be(false)
expect(windows.is_available()).to_be(false)
expect(freebsd.is_available()).to_be(false)
```

</details>

#### routes RV64 only through Linux descriptors

- routes RV64 only through Linux descriptors
   - Expected: linux_native.triple equals `riscv64-unknown-linux-gnu`
   - Expected: linux_native.linker equals `ld`
   - Expected: linux_cross.triple equals `riscv64-unknown-linux-gnu`
   - Expected: linux_cross.linker equals `riscv64-linux-gnu-ld`
   - Expected: macos.linker equals ``
   - Expected: windows.linker equals ``
   - Expected: freebsd.linker equals ``
   - Expected: macos.triple equals `riscv64-apple-darwin`
   - Expected: windows.triple equals `riscv64-pc-windows-msvc`
   - Expected: freebsd.triple equals `riscv64-unknown-freebsd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes RV64 only through Linux descriptors")
val linux_native = toolchain_riscv64("linux", "riscv64")
expect(linux_native.triple).to_equal("riscv64-unknown-linux-gnu")
expect(linux_native.linker).to_equal("ld")
expect(linux_native.requires_external).to_be(false)

val linux_cross = toolchain_riscv64("linux", "x86_64")
expect(linux_cross.triple).to_equal("riscv64-unknown-linux-gnu")
expect(linux_cross.linker).to_equal("riscv64-linux-gnu-ld")
expect(linux_cross.requires_external).to_be(true)

val macos = toolchain_riscv64("macos", "riscv64")
val windows = toolchain_riscv64("windows", "riscv64")
val freebsd = toolchain_riscv64("freebsd", "riscv64")
expect(macos.linker).to_equal("")
expect(windows.linker).to_equal("")
expect(freebsd.linker).to_equal("")
expect(macos.triple).to_equal("riscv64-apple-darwin")
expect(windows.triple).to_equal("riscv64-pc-windows-msvc")
expect(freebsd.triple).to_equal("riscv64-unknown-freebsd")
expect(macos.is_available()).to_be(false)
expect(windows.is_available()).to_be(false)
expect(freebsd.is_available()).to_be(false)
```

</details>

#### fails hosted RV32 closed without borrowing an RV64 toolchain

- fails hosted RV32 closed without borrowing an RV64 toolchain
   - Expected: toolchain.triple equals `riscv32-unknown-linux-gnu`
   - Expected: toolchain.linker equals ``
   - Expected: toolchain.sysroot equals ``
   - Expected: toolchain.crt_dir equals ``
   - Expected: toolchain.default_flags.len() equals `0`
   - Expected: hosted_cross_c_compiler_name("riscv32-unknown-linux-gnu", "linux", "x86_64") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails hosted RV32 closed without borrowing an RV64 toolchain")
val toolchain = toolchain_for_target(CodegenTarget.Riscv32)
expect(toolchain.triple).to_equal("riscv32-unknown-linux-gnu")
expect(toolchain.linker).to_equal("")
expect(toolchain.sysroot).to_equal("")
expect(toolchain.crt_dir).to_equal("")
expect(toolchain.default_flags.len()).to_equal(0)
expect(toolchain.is_available()).to_be(false)
expect(toolchain.diagnostic()).to_contain("No linker configured")
expect(toolchain.install_hint).to_contain("riscv32-unknown-none-elf")

val full = hosted_c_compiler_plan("riscv32-unknown-linux-gnu", "linux", "x86_64")
val alias = hosted_c_compiler_plan("rv32", "linux", "x86_64")
expect(full.supported).to_be(false)
expect(alias.supported).to_be(false)
expect(hosted_cross_c_compiler_name("riscv32-unknown-linux-gnu", "linux", "x86_64")).to_equal("")
```

</details>

#### uses a cross C compiler only for a Linux architecture mismatch

- uses a cross C compiler only for a Linux architecture mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses a cross C compiler only for a Linux architecture mismatch")
expect(hosted_cross_cc_required("aarch64-apple-darwin", "macos", "aarch64")).to_be(false)
expect(hosted_cross_cc_required("aarch64-unknown-freebsd", "freebsd", "aarch64")).to_be(false)
expect(hosted_cross_cc_required("aarch64-unknown-linux-gnu", "linux", "aarch64")).to_be(false)
expect(hosted_cross_cc_required("aarch64-unknown-linux-gnu", "linux", "x86_64")).to_be(true)
expect(hosted_cross_cc_required("riscv64-unknown-linux-gnu", "linux", "riscv64")).to_be(false)
expect(hosted_cross_cc_required("riscv64-unknown-linux-gnu", "linux", "x86_64")).to_be(true)
expect(hosted_cross_cc_required("", "freebsd", "aarch64")).to_be(false)
```

</details>

#### routes supported hosted cross links through the cross compiler

- routes supported hosted cross links through the cross compiler


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes supported hosted cross links through the cross compiler")
val source = read_file_text("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl") ?? ""
val cross_dispatch = source.index_of("if hosted_cross_cc_required(target, os, arch)")
val linker_discovery = source.index_of("val linker_result = find_linker()")
expect(cross_dispatch).to_be_greater_than(-1)
expect(linker_discovery).to_be_greater_than(cross_dispatch)
expect(source).to_contain("return link_native_cc(object_files, output, config)")
```

</details>

#### selects only supported Linux GNU AArch64 and RISC-V cross drivers

- selects only supported Linux GNU AArch64 and RISC-V cross drivers
   - Expected: hosted_cross_c_compiler_name("aarch64", "linux", "x86_64") equals `aarch64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("rv64", "linux", "x86_64") equals `riscv64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("aarch64-unknown-linux-gnu", "linux", "x86_64") equals `aarch64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("arm64-linux-gnu", "linux", "x86_64") equals `aarch64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("riscv64gc-unknown-linux-gnu", "linux", "x86_64") equals `riscv64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("rv64-linux-gnu", "linux", "aarch64") equals `riscv64-linux-gnu-gcc`
   - Expected: hosted_cross_c_compiler_name("aarch64-unknown-linux-gnu", "linux", "arm64") equals ``
   - Expected: hosted_cross_c_compiler_name("riscv64-unknown-linux-gnu", "linux", "riscv64") equals ``
   - Expected: hosted_cross_c_compiler_name("aarch64-apple-darwin", "linux", "x86_64") equals ``
   - Expected: hosted_cross_c_compiler_name("aarch64-unknown-freebsd", "freebsd", "x86_64") equals ``
   - Expected: hosted_cross_c_compiler_name("aarch64-unknown-linux-musl", "linux", "x86_64") equals ``
   - Expected: freebsd_cross.command equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects only supported Linux GNU AArch64 and RISC-V cross drivers")
expect(hosted_cross_c_compiler_name("aarch64", "linux", "x86_64")).to_equal("aarch64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("rv64", "linux", "x86_64")).to_equal("riscv64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("aarch64-unknown-linux-gnu", "linux", "x86_64")).to_equal("aarch64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("arm64-linux-gnu", "linux", "x86_64")).to_equal("aarch64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("riscv64gc-unknown-linux-gnu", "linux", "x86_64")).to_equal("riscv64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("rv64-linux-gnu", "linux", "aarch64")).to_equal("riscv64-linux-gnu-gcc")
expect(hosted_cross_c_compiler_name("aarch64-unknown-linux-gnu", "linux", "arm64")).to_equal("")
expect(hosted_cross_c_compiler_name("riscv64-unknown-linux-gnu", "linux", "riscv64")).to_equal("")
expect(hosted_cross_c_compiler_name("aarch64-apple-darwin", "linux", "x86_64")).to_equal("")
expect(hosted_cross_c_compiler_name("aarch64-unknown-freebsd", "freebsd", "x86_64")).to_equal("")
expect(hosted_cross_c_compiler_name("aarch64-unknown-linux-musl", "linux", "x86_64")).to_equal("")

val freebsd_cross = hosted_c_compiler_plan("aarch64-unknown-freebsd", "freebsd", "x86_64")
expect(freebsd_cross.requires_cross).to_be(true)
expect(freebsd_cross.supported).to_be(false)
expect(freebsd_cross.command).to_equal("")

val reverse = hosted_c_compiler_plan("x86_64-unknown-linux-gnu", "linux", "aarch64")
expect(reverse.requires_cross).to_be(true)
expect(reverse.supported).to_be(false)
val wrong_os = hosted_c_compiler_plan("aarch64-apple-darwin", "linux", "x86_64")
expect(wrong_os.supported).to_be(false)
```

</details>

#### rejects architecture mismatches

- rejects architecture mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects architecture mismatches")
expect(hosted_c_target_matches_host("aarch64-unknown-linux-gnu", "linux", "x86_64")).to_be(false)
expect(hosted_c_target_matches_host("riscv64-unknown-linux-gnu", "linux", "aarch64")).to_be(false)
expect(hosted_c_target_matches_host("x86_64-pc-windows-msvc", "windows", "aarch64")).to_be(false)
```

</details>

#### rejects operating-system mismatches

- rejects operating-system mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects operating-system mismatches")
expect(hosted_c_target_matches_host("x86_64-apple-darwin", "linux", "x86_64")).to_be(false)
expect(hosted_c_target_matches_host("aarch64-unknown-linux-gnu", "macos", "aarch64")).to_be(false)
expect(hosted_c_target_matches_host("x86_64-unknown-freebsd", "windows", "x86_64")).to_be(false)
```

</details>

#### rejects ABI mismatches and unsupported hosted widths

- rejects ABI mismatches and unsupported hosted widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects ABI mismatches and unsupported hosted widths")
expect(hosted_c_target_matches_host("x86_64-unknown-linux-musl", "linux", "x86_64")).to_be(false)
expect(hosted_c_target_matches_host("x86_64-pc-windows-gnu", "windows", "x86_64")).to_be(false)
expect(hosted_c_target_matches_host("riscv64-unknown-freebsd", "freebsd", "riscv64")).to_be(false)
expect(hosted_c_target_matches_host("rv64i-unknown-linux-gnu", "linux", "riscv64")).to_be(false)
expect(hosted_c_compiler_plan("riscv64be-unknown-linux-gnu", "linux", "x86_64").supported).to_be(false)
expect(hosted_c_target_matches_host("armv7-unknown-linux-gnueabihf", "linux", "armv7")).to_be(false)
```

</details>

#### guards before host C runtime and entry compilation

- guards before host C runtime and entry compilation


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guards before host C runtime and entry compilation")
val source = compiler_native_link_source()
val simpleos_guard = source.index_of("if is_simpleos_riscv32_link")
val hosted_plan = source.index_of("val hosted_plan = hosted_c_compiler_plan")
val hosted_guard = source.index_of("if not hosted_plan.supported")
val arch_guard = source.index_of("if not hosted_native_link_arch_supported")
val stage4_cross_guard = source.index_of("if stage4_requested and hosted_plan.requires_cross:")
val compiler_discovery = source.index_of("val hosted_cc = find_c_compiler()")
val runtime_compile = source.index_of("val rt_result = compile_runtime_objects")
val entry_compile = source.index_of("val c_result = compile_entry_point_c")
expect(simpleos_guard).to_be_greater_than(-1)
expect(hosted_plan).to_be_greater_than(simpleos_guard)
expect(hosted_guard).to_be_greater_than(hosted_plan)
expect(arch_guard).to_be_greater_than(hosted_guard)
expect(stage4_cross_guard).to_be_greater_than(arch_guard)
expect(compiler_discovery).to_be_greater_than(stage4_cross_guard)
expect(runtime_compile).to_be_greater_than(compiler_discovery)
expect(entry_compile).to_be_greater_than(runtime_compile)
expect(source).to_contain("Stage4 strict profile requires a native host target; cross-target compiler capsules are unavailable")
```

</details>

#### preserves explicit bare-metal mode in both direct LLVM paths

- preserves explicit bare-metal mode in both direct LLVM paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves explicit bare-metal mode in both direct LLVM paths")
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_codegen_adapter.spl") ?? ""
val predicate_start = source.index_of("fn llvm_codegen_bare_metal_requested")
val translate_start = source.index_of("pub fn llvm_translate_module_direct_ir")
val direct_start = source.index_of("pub fn llvm_compile_module_direct(")
val compiled_start = source.index_of("pub fn llvm_compile_module_direct_compiled")
val impl_start = source.index_of("impl Codegen for LlvmCodegenAdapter")
expect(predicate_start).to_be_greater_than(-1)
expect(translate_start).to_be_greater_than(predicate_start)
expect(direct_start).to_be_greater_than(translate_start)
expect(compiled_start).to_be_greater_than(direct_start)
expect(impl_start).to_be_greater_than(compiled_start)

val helpers = source.substring(predicate_start, translate_start)
val translate = source.substring(translate_start, direct_start)
val direct = source.substring(direct_start, compiled_start)
val compiled = source.substring(compiled_start, impl_start)
expect(helpers).to_contain("mir_target_context_os_from(requested_target, \"\") == \"baremetal\"")
expect(helpers).to_contain("LlvmTargetConfig.for_target_portable_numeric_baremetal")
expect(helpers).to_contain("LlvmTargetConfig.for_target_portable_numeric(options.target")
expect(helpers).to_contain("MirToLlvm.create_baremetal")
expect(helpers).to_contain("MirToLlvm.create(module_name")
expect(translate).to_contain("llvm_codegen_translator(module.name, options.target)")
expect(direct).to_contain("llvm_codegen_target_config(options)")
expect(compiled).to_contain("llvm_codegen_target_config(options)")
expect(compiled).to_contain("llvm_codegen_translator(\"app.cli.bootstrap_main\", options.target)")
```

</details>

#### guards every shared native linker caller before bundle or platform dispatch

- guards every shared native linker caller before bundle or platform dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guards every shared native linker caller before bundle or platform dispatch")
val source = rt_file_read_text("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl") ?? ""
val os_guard = source.index_of("if not hosted_native_link_os_supported")
val arch_guard = source.index_of("if not hosted_native_link_arch_supported")
val bundle_dispatch = source.index_of("val smf_inputs = filter_smf_inputs")
val platform_dispatch = source.index_of("# Platform-specific linking")
expect(os_guard).to_be_greater_than(-1)
expect(arch_guard).to_be_greater_than(os_guard)
expect(bundle_dispatch).to_be_greater_than(arch_guard)
expect(platform_dispatch).to_be_greater_than(bundle_dispatch)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted C target guard.
- hosted C target guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `b16b8d0603d78ca6bb69c2eb8bc5e1e7d51519e0cb82ee0049b59cd5ad4bfc29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b16b8d0603d78ca6bb69c2eb8bc5e1e7d51519e0cb82ee0049b59cd5ad4bfc29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b16b8d0603d78ca6bb69c2eb8bc5e1e7d51519e0cb82ee0049b59cd5ad4bfc29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/hosted_c_target_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/hosted_c_target_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/hosted_c_target_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows implicit and explicit host targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows same-host architecture aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows matching Linux architectures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
