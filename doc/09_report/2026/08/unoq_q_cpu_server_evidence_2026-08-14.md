# UNO Q CPU-only server evidence — 2026-08-14

## Result

`SimpleOsServerExecutionReceiptV1` status: **WARN / blocked**.

The connected board is the physical Arduino UNO Q QRB2210-family Linux MPU,
but it is booted into Debian 13 rather than SimpleOS.  No Simple runtime or
web/database server executable is installed on its filesystem.  A current
source AArch64 web artifact could not be produced because the Stage-2 compiler
did not resolve the example module imports; the database artifact reached the
linker but the host lacks AArch64 `zlib`, `zstd`, and `tinfo` link libraries.
Consequently no executable was deployed, no host-visible HTTP/DB probe was
run, and CPU-only server acceptance is not claimed.

## SimpleOsServerExecutionReceiptV1

```text
receipt_version=SimpleOsServerExecutionReceiptV1
mode=unoq-cpu
step=Launch UNO Q server executable
helper=uno_q_server_fixture
status=blocked
timestamp_utc=2026-08-14T04:39:12Z
source_revision=8884df02847316906feda5c8ae39c0f65c3a136e
adb_serial=3655308719
hostname=uno-q
architecture=aarch64
kernel=Linux uno-q 6.16.7-g0dd6551ae96b #1 SMP PREEMPT Tue Sep 23 12:46:06 UTC 2025 aarch64 GNU/Linux
os_release=Debian GNU/Linux 13 (trixie)
device_tree_model=Arduino SA,Imola
device_tree_compatible=arduino,imola|qcom,qcm229n|qcom,qrb221n
root_filesystem=/dev/mmcblk0p68 ext4 rw,relatime
boot_id=e5bd8b78-9719-4a98-acba-11a0ef34980e
identity_sha256=4cc26119e85f60e4f5607ed1992ff45c8126ce4f4dae12c9a94250eccf306044
safe_remote_workspace=/tmp
simpleos_boot=false
server_executable=absent
server_executable_sha256=absent
filesystem_launch=false
http_probe=false
database_probe=false
restart_persistence_probe=false
gpu_selected=false
cpu_only_probe=false
mutable_state_owner=host-parent
boundary_result=encoded-receipt
raw_pointer_transport=false
reason=current-source-aarch64-server-artifact-unavailable-and-board-is-not-booted-into-simpleos
```

## Commands and retained build receipts

Every ADB command was serialized with
`flock /tmp/unoq-server-matrix.lock`.  Inventory was read-only; no board files
were created or changed.

The identity command queried `/etc/os-release`, `/proc/cpuinfo`, device-tree
model/compatibility, root mount, boot ID, DRM devices, Vulkan availability,
and executable inventory under `/home/arduino`, `/usr/local/bin`, and `/opt`.
It exited 0.  `/data/local/tmp` is absent; `/tmp` and `/home/arduino` are the
available recoverable workspaces.  No executable matching `simple`,
`*simple*server*`, or `simpleos-*` was found.

The user-authorized temporary Stage-2 compiler was
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA-256
`5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`.
It is diagnostic only and supplies no Stage-4 acceptance credit.

- Web build attempts 1 and 2 exited 1. Both logs have SHA-256
  `2f328e957476c97c5a6c89a96c8c1c5bdde5314ac19239c633ad385c28c2d486`.
  The terminal failure was HIR `ANY.static_root` after unresolved
  `examples.simple_web_server` imports. Repeating with the corrected source
  root produced the same result, so no third attempt was made.
- Database build attempt 1 exited 1. Its log has SHA-256
  `7b8801530dcb46d2c33916752ba260519d79041e9a76ee51c9c3644994befb77`.
  AArch64 compilation reached link, then failed because `-lz`, `-lzstd`, and
  `-ltinfo` were unavailable. The produced objects are not an executable and
  were not deployed.

## Acceptance disposition

- AC-4: partial identity/mount/source receipt only; executable hash is absent.
- AC-5: blocked before deploy, HTTP, DB, and restart probes.
- AC-6: blocked because there is no server workload to execute in a forced
  CPU-only environment. `gpu_selected=false` records observation, not proof.
- AC-8: not exercised. The parent-owner and encoded pointer-free receipt shape
  is a design contract only; no server or worker ran and no acceptance credit
  is claimed.

The frozen helpers `expect_http_file`, `expect_db_reboot`, and
`expect_cpu_mode` must fail for this receipt. Promotion requires a
provenance-admitted AArch64 server artifact and a physical SimpleOS QRB2210
boot; Debian userspace execution must never be relabeled as SimpleOS.
