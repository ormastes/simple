# SimpleOS ARM64 server QEMU preflight — 2026-08-14

STATUS: FAIL

The mandatory preflight stopped this lane before payload build or QEMU. The
5 GiB storage floor, QEMU executable, and base ARM64 sysroot now pass. The
current-source compiler and pure-Simple target runtime remain absent, so the
sysroot archive is only a partial libc/C-runtime prerequisite. The existing ARM64
server ELF is recorded only as an inadmissible stale/unproven artifact; it was
not executed.

```text
arm_qemu_server_preflight_version=2
workspace=/mnt/data/worktrees/restart12-servers
storage_floor_bytes=5368709120
storage_available_bytes=1195233558528
storage_floor=PASS
qemu_aarch64=PASS path=/usr/bin/qemu-system-aarch64
current_simple_compiler=FAIL reason=no-executable-current-source-compiler
current_simple_compiler_cycle3=FAIL exit=1 elapsed=4m39.91s max_rss_kib=799944 reason="bootstrap-circular GlobalLoad plus proof_uses inference and frontend timeout"
sysroot_crt0=PASS path=build/os/sysroot-aarch64/lib/crt0.o required=file
sysroot_os_archive=PASS_PARTIAL path=build/os/sysroot-aarch64/lib/libsimpleos_all.a required=file note="libc+C-runtime only; pure-Simple core objects absent"
sysroot_cc=PASS path=build/os/sysroot-aarch64/lib/cc-aarch64-simpleos required=exec
sysroot_linker=PASS path=build/os/sysroot-aarch64/share/simpleos/simpleos.ld required=file
target_runtime=FAIL path=build/os/simple-core-simpleos-aarch64/libsimple_runtime.a required=file
server_entry=PASS path=src/os/apps/servers_user/main.spl bytes=10264
filesystem_entry=PASS path=examples/09_embedded/simple_os/arch/arm64/servers_entry.spl bytes=1620
payload_builder=PASS path=scripts/os/build_arm64_servers_payload.shs bytes=2311
existing_server_payload=present path=build/os/arm64_servers/servers.elf machine=AArch64 bytes=8288 sha256=90b914dcc3dae802b19378e81a4a56dd62ea56fe9fe0643414216b947bc29852
preflight_result=FAIL
preflight_reason=missing-current-source-compiler-and-pure-simple-target-runtime
build_attempted=false
qemu_launched=false
```

After the preflight, the base sysroot and 18-part target runtime archive were
produced. One diagnostic Stage-2 payload build then reached the linker and
failed on `rt_array_enumerate`, `rt_file_rename`, `bytes_to_string`,
`rt_arm64_syscall`, and `rt_unwrap_or_trap`; retained objects are under
`.simple/native-objects-jWARot`. This is bootstrap diagnostic evidence only.

After bounded owner fixes, final payload-link cycle 3 succeeded using the
existing pure-Simple Stage-2: 57 current modules compiled, zero failed, and a
382 KiB static AArch64 ELF was produced at
`build/os/arm64_servers/servers.elf` with SHA-256
`33c9dc640e3aa1a031de68d22869ba7867a14cd174966cf875fc596bd19fd481`.
This remains bootstrap diagnostic evidence until a current-source compiler and
live QEMU HTTP/database/reboot receipts exist.

Consequently AC-1 through AC-3 and AC-10 remain open. No x86, marker, toy,
host-userspace, or pre-existing payload result was substituted. The canonical
current-source filesystem server gate, real VirtIO-network host HTTP probes,
and same-filesystem fresh-boot database readback were not attempted.
