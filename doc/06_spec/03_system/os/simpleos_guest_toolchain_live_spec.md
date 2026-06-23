# Simpleos Guest Toolchain Live Specification

> 1. dir create all

<!-- sdn-diagram:id=simpleos_guest_toolchain_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_guest_toolchain_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_guest_toolchain_live_spec -> std
simpleos_guest_toolchain_live_spec -> os
simpleos_guest_toolchain_live_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_guest_toolchain_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Guest Toolchain Live Specification

## Scenarios

### SimpleOS guest toolchain live lane

#### boots the SSH live guest and proves the staged toolchain surface in-guest

1. dir create all
   - Expected: disk_result.is_ok() is true
   - Expected: media_ready is true
2. rt file delete
3. Ok
4. rt file write text
5. rt file write text
6. remote error = remote ok error
7. remote error = remote ok error
8. "cat >/tmp/hello c <<'EOF'\nint main
9. "cat >/tmp/cmake-smoke/CMakeLists txt <<'EOF'\ncmake minimum required
10. "cat >/tmp/cmake-smoke/hello c <<'EOF'\nint main
11. remote error = remote ok error
12. remote error = remote ok error
13. remote error = remote ok error
14. "cat >/tmp/main rs <<'EOF'\nfn main
15. remote error = remote failure error
16. final serial = read serial log
17. rt file write text
18. rt file write text
19. rt file delete
   - Expected: stopped is true
   - Expected: ready is true
20. fail
   - Expected: final_serial contains `[boot]`
21. Err
22. rt file delete
23. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 98 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not live_guest_toolchain_enabled():
    print "[simpleos_guest_toolchain_live_spec] set SIMPLEOS_QEMU_SSH_TOOLCHAIN_LIVE=1 and install sshpass to run"
    expect(live_guest_toolchain_enabled()).to_equal(false)
else:
    val target = get_ssh_live_target()
    val port_result = allocate_live_host_port(33000)
    expect(port_result.is_ok()).to_equal(true)
    if port_result.is_err():
        return
    val host_port = port_result.unwrap()
    val built = build_os_with_backend(target, "llvm")
    if not built:
        print "[simpleos_guest_toolchain_live_spec] live guest build blocked before boot; see [build] stderr tail above for the current named blocker"
        expect(built).to_equal(false)
    else:
        val runnable = can_run_target(target)
        expect(runnable).to_equal(true)
        if runnable:
            dir_create_all("build/os")
            val run_token = "toolchain_{rt_getpid()}_{rt_time_now_unix_micros()}"
            val disk_result = _prepare_run_disk(run_token)
            expect(disk_result.is_ok()).to_equal(true)
            if disk_result.is_err():
                return
            val run_disk = disk_result.unwrap()
            val scenario = _scenario_x64_ssh_on_port(host_port, run_disk)
            val media_ready = ensure_scenario_media(scenario)
            expect(media_ready).to_equal(true)
            if not media_ready:
                if rt_file_exists(run_disk):
                    rt_file_delete(run_disk)
                return
            val qmp_socket = "/tmp/simpleos_guest_toolchain_live_{run_token}.sock"
            val serial_log = "build/os/simpleos_guest_toolchain_live_{run_token}.log"

            match spawn_guest_with_qmp_scenario(target, scenario, qmp_socket, serial_log):
                Ok(handle):
                    val ready = wait_for_serial_marker(handle, "[sshd] SSH daemon listening on port 22", 30000)
                    val boot_serial = read_serial_log(handle)
                    val boot_stderr = read_qemu_stderr_log(handle)
                    if not ready:
                        rt_file_write_text("build/os/simpleos_guest_toolchain_live_failure.log", boot_serial)
                        rt_file_write_text("build/os/simpleos_guest_toolchain_live_failure.stderr.log", boot_stderr)
                    var remote_error: text? = nil
                    var final_serial = boot_serial
                    if ready:
                        remote_error = remote_ok_error(host_port, "clang --version", "clang version")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port, "clang --print-target-triple", "x86_64-simpleos")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port,
                            "cat >/tmp/hello.c <<'EOF'\nint main(void) { return 0; }\nEOF\n" +
                            "clang --target=x86_64-simpleos --sysroot=/usr -c /tmp/hello.c -o /tmp/hello.o && " +
                            "test -f /tmp/hello.o && echo OBJECT_OK",
                            "OBJECT_OK")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port,
                            "ld.lld -T /usr/share/simpleos/simpleos.ld /usr/lib/crt0.o /tmp/hello.o -L /usr/lib -lsimpleos_c -o /tmp/hello.elf && " +
                            "test -f /tmp/hello.elf && echo LINK_OK",
                            "LINK_OK")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port,
                            "mkdir -p /tmp/cmake-smoke && " +
                            "cat >/tmp/cmake-smoke/CMakeLists.txt <<'EOF'\ncmake_minimum_required(VERSION 3.10)\nproject(hello C)\nadd_executable(hello hello.c)\nEOF\n" +
                            "cat >/tmp/cmake-smoke/hello.c <<'EOF'\nint main(void) { return 0; }\nEOF\n" +
                            "cmake -S /tmp/cmake-smoke -B /tmp/cmake-build -G Ninja >/tmp/cmake.log 2>&1 && " +
                            "ninja -C /tmp/cmake-build >/tmp/ninja.log 2>&1 && " +
                            "test -f /tmp/cmake-build/hello && echo CMAKE_NINJA_OK",
                            "CMAKE_NINJA_OK")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port, "rustc --print target-list", "x86_64-unknown-simpleos")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port, "rustc --print sysroot", "/usr")
                        if remote_error == nil:
                            remote_error = remote_ok_error(host_port, "rustc --print simpleos-wrapper-status", "status=report-and-gate")
                        if remote_error == nil:
                            remote_error = remote_failure_error(host_port,
                            "cat >/tmp/main.rs <<'EOF'\nfn main() {}\nEOF\nrustc /tmp/main.rs",
                            "status=report-and-gate")
                        if remote_error == nil:
                            remote_error = remote_failure_error(host_port, "cargo build", "status=report-and-gate")
                        final_serial = read_serial_log(handle)
                        if remote_error != nil:
                            rt_file_write_text("build/os/simpleos_guest_toolchain_live_failure.log", final_serial)
                            rt_file_write_text("build/os/simpleos_guest_toolchain_live_failure.stderr.log", boot_stderr)
                    val stopped = stop_guest(handle)
                    if rt_file_exists(run_disk):
                        rt_file_delete(run_disk)
                    expect(stopped).to_equal(true)
                    expect(ready).to_equal(true)
                    if ready:
                        if val err = remote_error:
                            fail(err)
                        expect(final_serial.contains("[boot]")).to_equal(true)
                Err(err):
                    if rt_file_exists(run_disk):
                        rt_file_delete(run_disk)
                    fail("failed to spawn guest: {err}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_guest_toolchain_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS guest toolchain live lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
