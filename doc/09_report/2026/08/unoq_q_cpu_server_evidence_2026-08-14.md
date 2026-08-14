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

## Concurrent verification refresh — 2026-08-14T05:34:51Z

Physical-board access was serialized with
`flock /tmp/unoq-server-matrix.lock`. The read-only identity refresh again
observed ADB serial `3655308719`, device-tree model `Arduino SA,Imola`,
compatibility `arduino,imola|qcom,qcm2290|qcom,qrb2210`, AArch64 Linux kernel
`6.16.7-g0dd6551ae96b`, Debian 13.4, ext4 root `/dev/mmcblk0p68`, and boot ID
`e5bd8b78-9719-4a98-acba-11a0ef34980e`. This is exact physical-board identity
evidence, but it is not SimpleOS identity evidence.

Every canonical SimpleOS compiler/loader filesystem path required by the
verification contract was absent, as was
`/usr/bin/simpleos-unoq-2d-evidence`. Therefore a filesystem executable could
not be launched; CPU-only HTTP/database/restart receipts and GPU
submit/fence/device-readback receipts remain absent. The canonical live GPU
wrapper exited 2 with `pure-simple-runtime-missing` before board mutation, so
it supplies only a fail-closed blocker receipt and no provider/runtime credit.

Retained local evidence:

- `build/unoq-server-matrix/verify-20260814/identity.log` — SHA-256
  `266cf122ca291b9b477542464dd1dcd8269f6f691174eb59a7fdd6b33f11cde9`
- `build/unoq-server-matrix/verify-20260814/gpu-gate.log` — SHA-256
  `9797668b837e5ca35a599447886ab8bb5821c79f0956a0bee73f6e76232a9e5b`
- `build/unoq-server-matrix/verify-20260814/status.env` — SHA-256
  `b754eae3f584323a8416a6ec55ced5729e9bc31a30ec918dab059801f87810f7`
- `build/unoq-server-matrix/verify-20260814/SHA256SUMS` — checksum manifest

Verification disposition: **STATUS: FAIL / BLOCKED-TARGET-RUNTIME**. Debian
execution and Vulkan enumeration are explicitly not accepted as SimpleOS.

## Final atomic serialized receipt — 2026-08-14T08:11:52Z

The canonical producer acquired `/tmp/unoq-server-matrix.lock`, staged the
complete receipt in a private temporary directory, and published it once by
atomic rename. Its retained `producer.snapshot.shs` bytes and current producer
both hash to
`5a2f7e3aa68551461ecc5d8b63854f6a930965bf74072fcb456194de5d2a2c70`.

The receipt binds HEAD `900f9188ac50182f8f95505639072e9b1d9f7e2e`, ADB serial
`3655308719`, model `Arduino SA,Imola`, architecture `aarch64`, Debian GNU/Linux
13 (trixie), and boot ID `e5bd8b78-9719-4a98-acba-11a0ef34980e`.

CPU absence is proven by the exact retained command
`test -x scripts/check/run-unoq-qrb2210-cpu-server-live.shs`, exit 1, command
SHA-256 `c600080f47b50bc36aabc181c78011775967574f31ef8d8dc917e84541394d28`.
CPU acceptance remains **BLOCKED**; no CPU runner or server command executed.

Final receipt:
`build/test-artifacts/simpleos-server-execution-matrix/uno-q/verify-20260814T081152Z/`.
`status.env` SHA-256 is
`718ddcde312abbdadb60556e0d455047fb0edc3620c7d2776af2eec00efdb93d`;
`command-receipts.env` SHA-256 is
`51f1f36628e4e81cd8c47326de4ebbbb1d281ec689dd6ec6ff716d2780d38682`;
the manifest SHA-256 is
`7bf25984e57dfb0fa3db2ebeb4cba9d75a9efa20a499127543205bb1510bcbed`.
The one permitted checksum verification passed every entry.

## Canonical CPU runner source completion

`scripts/check/run-unoq-qrb2210-cpu-server-live.shs` now exists. The preceding
receipt's executable-absence result remains historically correct for its frozen
HEAD/time, but no longer describes the working tree.

The new runner fails before board access unless it receives an admitted
current-source AArch64 server ELF, the exact
`simpleos-arm64-current-source-compiler-admission-v1` receipt, and its bound
source manifest. Physical execution additionally requires authoritative
SimpleOS QRB2210 boot/bundle/recovery identity; Debian is rejected. PASS demands
forced CPU selection with accelerator providers/libraries, GPU submission, and
device readback explicitly false, plus HTTP filesystem-byte equality and an
authenticated DB commit/read/fresh-reboot/read receipt. Credential material is
ephemeral and must be reported destroyed with no retained bytes.

Only the negative self-test ran. It passed without ADB access. No live CPU
runner, board command, deployment, download, reboot, or acceptance was run or
claimed. CPU status remains **BLOCKED** pending admitted artifacts and an
authorized physical SimpleOS boot.

Cycle-2 review aligned the runner with the actual compiler admission fields:
`native_smoke_output_sha256`, `source_revision`, source-manifest hash,
`native_smoke_status=pass`, and `stub_fallback=forbidden`. Remote provenance
must bind that source revision, manifest, compiler-admission hash, signed bundle,
and provider hash. All security hashes are unique lowercase 64-hex values.

The host now observes live process maps and file descriptors, rejects loaded
accelerator libraries and device nodes, verifies distinct pre/post reboot boot
IDs, compares HTTP expected/body hashes and DB before/after hashes with a
positive generation, rehashes server/provider bytes after reboot, and proves
remote receipt cleanup. Collector lock handoff uses a validated inherited file
descriptor, not an environment boolean. Expanded synthetic sabotage remains
negative-only. No physical runner was invoked.

Cycle 3 makes collector status and mutation fields derived from validated runner
stdout/exit, validates and retains the inherited flock FD, binds both phase PIDs
through executable/cmdline/maps/fds, and moves HTTP, DB, reboot, and credential
observations to the host. Output escape/symlink checks precede directory
creation, and failure/signal cleanup covers processes, receipts, forwards, and
credential material. This remains source/negative evidence only.

Independent final review status: **FAIL**. The source improvements above do not
yet constitute host-authoritative acceptance evidence. Blocked post-mutation
exits can still be summarized as non-mutating; cleanup is not complete and
checked on every terminal path; credential scanning is provider-selected; HTTP
and authenticated DB response grammar are not validated exactly; boot
provenance is not bound to a locally trusted signed manifest; and collector
producer, exit, and collision evidence is incomplete. The three-cycle cap is
exhausted. No live invocation is authorized and no AC is credited.

## Source-only blocker repair

A fresh bounded lane implemented the rejected runner/collector contracts:
phase-aware mutation records, checked cleanup with scrubbed diagnostic
retention, bounded host-owned credential scanning, strict HTTP and authenticated
DB transcript hashes, signed locally pinned boot-manifest trust, CPU-runner
snapshot/exit binding, aggregate exit propagation, and collision refusal. Its
negative sabotage is ADB-free. No board was accessed and the historical
FAIL/BLOCKED acceptance disposition remains unchanged.
