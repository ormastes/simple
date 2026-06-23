# Simpleos Guest Toolchain Wrapper Specification

> 1. cleanup tmpdir

<!-- sdn-diagram:id=simpleos_guest_toolchain_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_guest_toolchain_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_guest_toolchain_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_guest_toolchain_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Guest Toolchain Wrapper Specification

## Scenarios

### SimpleOS guest toolchain wrapper

#### clang reports guest-exec status and forwards supported LLVM operations

1. cleanup tmpdir
2. fail
3. cleanup tmpdir
4. fail
   - Expected: triple_out.trim() equals `x86_64-simpleos`
5. cleanup tmpdir
6. fail
7. cleanup tmpdir
8. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = setup_wrapper_fixture()
val status_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' --print simpleos-wrapper-status"
val (status_out, status_err, status_code) = run_shell(status_cmd)
if status_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang status command failed: {status_out}{status_err}")
expect(status_out).to_contain("lane=x86_64-simpleos")
expect(status_out).to_contain("mode=native-wrapper")
expect(status_out).to_contain("status=guest-exec")

val triple_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' --print-target-triple"
val (triple_out, triple_err, triple_code) = run_shell(triple_cmd)
if triple_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang triple command failed: {triple_out}{triple_err}")
expect(triple_out.trim()).to_equal("x86_64-simpleos")

val exec_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' -c /tmp/hello.c -o /tmp/hello.o"
val (exec_out, exec_err, exec_code) = run_shell(exec_cmd)
if exec_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang exec command failed: {exec_out}{exec_err}")
expect(exec_out).to_contain("LLVM_PAYLOAD -c /tmp/hello.c -o /tmp/hello.o")

val link_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/ld.lld' /tmp/hello.o -o /tmp/hello.elf"
val (link_out, link_err, link_code) = run_shell(link_cmd)
cleanup_tmpdir(tmpdir)
if link_code != 0:
    fail("ld.lld exec command failed: {link_out}{link_err}")
expect(link_out).to_contain("LLD_PAYLOAD /tmp/hello.o -o /tmp/hello.elf")
```

</details>

#### cmake and ninja expose the supported configure lane

1. cleanup tmpdir
2. fail
3. cleanup tmpdir
4. fail
5. cleanup tmpdir
6. fail
7. cleanup tmpdir
8. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = setup_wrapper_fixture()
val caps_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cmake' -E capabilities"
val (caps_out, caps_err, caps_code) = run_shell(caps_cmd)
if caps_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("cmake capabilities failed: {caps_out}{caps_err}")
expect(caps_out).to_contain("serverMode=false")
expect(caps_out).to_contain("lane=x86_64-simpleos")
expect(caps_out).to_contain("status=report-and-gate")

val cfg_cmd =
    "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cmake' " +
    "-S '{tmpdir}/src' -B '{tmpdir}/build' -G Ninja"
val (cfg_out, cfg_err, cfg_code) = run_shell(cfg_cmd)
if cfg_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("cmake configure failed: {cfg_out}{cfg_err}")
expect(cfg_out).to_contain("Build files have been written to: {tmpdir}/build")

val ninja_file_cmd =
    "grep -q '/usr/bin/clang' '{tmpdir}/build/build.ninja' && " +
    "grep -q '/usr/bin/ld.lld' '{tmpdir}/build/build.ninja'"
val (_, _, ninja_file_code) = run_shell(ninja_file_cmd)
if ninja_file_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("generated build.ninja does not reference the stable guest tool paths")

val ninja_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/ninja' -C '{tmpdir}/build'"
val (ninja_out, ninja_err, ninja_code) = run_shell(ninja_cmd)
cleanup_tmpdir(tmpdir)
if ninja_code != 0:
    fail("ninja wrapper failed: {ninja_out}{ninja_err}")
expect(ninja_out).to_contain("NINJA_PAYLOAD -C {tmpdir}/build")
```

</details>

#### rust wrappers expose discovery and reject unsupported build operations

1. cleanup tmpdir
2. fail
3. cleanup tmpdir
4. fail
   - Expected: target_out.trim() equals `/usr/lib/rustlib/x86_64-unknown-simpleos/lib`
   - Expected: rust_fail_code equals `1`
5. cleanup tmpdir
   - Expected: cargo_fail_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = setup_wrapper_fixture()
val status_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' --print simpleos-wrapper-status"
val (status_out, status_err, status_code) = run_shell(status_cmd)
if status_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("rustc status failed: {status_out}{status_err}")
expect(status_out).to_contain("lane=x86_64-simpleos")
expect(status_out).to_contain("status=report-and-gate")

val target_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' --print target-libdir"
val (target_out, target_err, target_code) = run_shell(target_cmd)
if target_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("rustc target-libdir failed: {target_out}{target_err}")
expect(target_out.trim()).to_equal("/usr/lib/rustlib/x86_64-unknown-simpleos/lib")

val rust_fail_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' main.rs"
val (_rust_fail_out, rust_fail_err, rust_fail_code) = run_shell(rust_fail_cmd)
expect(rust_fail_code).to_equal(1)
expect(rust_fail_err).to_contain("lane=x86_64-simpleos")
expect(rust_fail_err).to_contain("mode=native-wrapper")
expect(rust_fail_err).to_contain("status=report-and-gate")
expect(rust_fail_err).to_contain("no host fallback")

val cargo_fail_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cargo' build"
val (_cargo_fail_out, cargo_fail_err, cargo_fail_code) = run_shell(cargo_fail_cmd)
cleanup_tmpdir(tmpdir)
expect(cargo_fail_code).to_equal(1)
expect(cargo_fail_err).to_contain("lane=x86_64-simpleos")
expect(cargo_fail_err).to_contain("status=report-and-gate")
expect(cargo_fail_err).to_contain("no host fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS guest toolchain wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
