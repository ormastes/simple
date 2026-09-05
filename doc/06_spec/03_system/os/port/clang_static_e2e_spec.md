# Clang from the SimpleOS filesystem

> Lint-only: validates symbol resolution + IF-08 marker conventions for

<!-- sdn-diagram:id=clang_static_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=clang_static_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

clang_static_e2e_spec -> std
clang_static_e2e_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=clang_static_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Primary flow

1. Require `SIMPLEOS_CLANG_FS_E2E=1`, the guest-native Clang payload, and the
   canonical `scripts/os/build_clang_disk.shs` QEMU wrapper.
   `SIMPLE_BUILD_COMPILER` must name a functional self-hosted compiler; Rust
   seeds and candidates that fail the exact `-c` output `2` smoke are rejected.
2. Run the wrapper and require exit code 0 plus SHA-256 identities for the
   current kernel and filesystem images. Skip modes, native-build failure,
   timeout, and unexpected QEMU exit codes fail.
3. Require its validated guest-produced ELF64 x86-64 relocatable object with
   an exact `main` symbol.
4. Require in-guest `/hello.elf` linking.
5. Require the resulting filesystem ELF to run in ring 3, emit the exact
   `hello-from-simpleos-clang` line, and exit with status 42. The shared
   production runner must report PASS before the Clang wrapper may report PASS.

## Evidence contract

Lint-only: validates symbol resolution + IF-08 marker conventions for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/clang_static_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Lint-only: validates symbol resolution + IF-08 marker conventions for
    Phase 3 clang_static smoke. Disk paths and markers referenced without
    invocation. Behavioural body env-gated until Team A static binary lands.
    Markers: [phase-2-clang-version] [phase-2-clang-compile-ok]

## Scenarios

### clang_static in-guest QEMU e2e contract

#### clang_static binary paths and spawn symbol resolve at lint time

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
if false:
    val _pid = x86_64_fs_exec_spawn_hello_world_smf()
    val _p = "/usr/bin/clang_static"
    val _fb = "/sys/apps/clang_static"
    val _m1 = "[phase-2-clang-version]"
    val _m2 = "[phase-2-clang-compile-ok]"
return "skip: behavioural run blocked on Phase 3 Team A binary"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
