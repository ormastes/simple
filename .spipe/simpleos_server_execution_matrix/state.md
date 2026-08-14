# SPipe state: SimpleOS server execution matrix

## Goal

Prove filesystem-backed web and database server executables on ARM64 QEMU and
the physical Arduino UNO Q QRB2210, including separate CPU-only and
GPU-accelerated UNO Q runs.

## Acceptance criteria

- [ ] AC-1: A current-source ARM64 SimpleOS image boots in QEMU and launches a
  real server executable from its mounted filesystem.
- [ ] AC-2: The ARM64 guest answers HTTP health and filesystem-document requests
  over a host-visible socket.
- [ ] AC-3: The ARM64 guest accepts a DB write/read and observes the committed
  value after a fresh boot against the same filesystem image.
- [ ] AC-4: The physical UNO Q identity, kernel/OS context, filesystem mount,
  executable hash, and source commit are retained in one receipt.
- [ ] AC-5: UNO Q launches the web/DB server executable from its filesystem and
  completes real HTTP file plus DB write/read/restart probes.
- [ ] AC-6: A forced CPU-only UNO Q run proves the server/filesystem workload
  with GPU devices disabled or unselected.
- [ ] AC-7: A GPU-accelerated UNO Q run proves selected Adreno/Vulkan device,
  submit, fence/completion, and device-readback while the server/filesystem
  workload remains live.
- [ ] AC-8: CPU/GPU boundary data is copied/frozen or handle-bound; mutable
  server/DB/filesystem state remains owned by one parent and commits validated
  child/device results deterministically.
- [ ] AC-9: Manuals, guide, requirements, architecture/design, executable specs,
  and retained receipts trace every matrix cell without placeholder passes.
- [ ] AC-10: Highest-capability review accepts implementation and evidence; all
  required static/runtime gates pass once.
- [ ] AC-11: Intentional changes are committed, rebased and pushed under the
  restart12 lock, then proven reachable from refetched `origin/main`.
- [ ] AC-12: A retained Linux benchmark compares equivalent Simple HTTP and DB
  operations with nginx, PostgreSQL, and SQLite using fixed CPU, concurrency,
  durability, dataset, p50/p95, throughput, and RSS controls.
- [ ] AC-13: CPU-only and CUDA-assisted rows state the exact workload boundary;
  CUDA receives immutable/owned input and returns a validated result, while
  socket, database, and filesystem state remains parent-owned.
- [ ] AC-14: CUDA is an optional dynload feature and is neither loaded nor
  required by the CPU-only server executable/path.
- [ ] AC-15: Any measured Simple deficit is addressed with at most three
  semantics-preserving Pure-Simple optimization cycles, or retained as a
  measured compiler/runtime/architecture blocker without weakening semantics.

## Frozen interfaces and manual vocabulary

- Receipt: `SimpleOsServerExecutionReceiptV1`.
- Modes: `qemu-arm64-cpu`, `unoq-cpu`, `unoq-gpu`.
- Steps: `Boot ARM QEMU server executable`; `Serve a filesystem document over
  HTTP`; `Persist and reload a database value`; `Launch UNO Q server
  executable`; `Verify UNO Q CPU-only path`; `Verify UNO Q GPU-accelerated
  path`.
- Helpers: `arm_qemu_server_fixture`, `uno_q_server_fixture`,
  `expect_http_file`, `expect_db_reboot`, `expect_cpu_mode`,
  `expect_gpu_receipt`.
- Mutable server/DB/filesystem state is parent-owned. QEMU/device results cross
  boundaries as encoded receipts or validated handles, never raw pointers.
- Missing execution helpers must fail with `fail(...)` or `assert(false)`.

## Phase

dev-active

## Log

- dev: Added 11 acceptance criteria from the user-selected ARM QEMU and UNO Q
  executable CPU/GPU matrix.
- dev: Added the user-selected Linux nginx/PostgreSQL/SQLite CPU/CUDA
  comparison, optional-dynload, and measured optimization criteria.
- dev-blocked: ARM64 mounted ELFs lack file syscalls 30--33 and network
  syscalls 70--76; ARM `rt_net_*` is stubbed and the mounted ELF is a marker.
  Real AC-1..3 require ARM virtio-net/TCP, EL0 pointer marshaling, and durable
  FAT32 writes. ARM KVM is unavailable on this x86_64 host, so faithful QEMU
  execution would use TCG.
- dev-blocked: The connected UNO Q is Arduino Imola/aarch64 Debian 13 with
  Adreno 702 exposed through Turnip, but the canonical physical-board gate
  stopped with `pure-simple-runtime-missing` and
  `/usr/bin/simpleos-unoq-2d-evidence` is absent. This proves hardware identity,
  not SimpleOS GPU execution; AC-7 remains open.
- dev-blocked: The UNO Q filesystem is Debian ext4 and contains no SimpleOS
  server executable. Cross-building web reached an unresolved-import HIR
  failure and DB linking lacked target zlib/zstd/tinfo; AC-4 has identity-only
  evidence and AC-5/6 remain open. No board files were modified.
- dev-blocked: The fresh Linux HTTP artifact reported ready without binding a
  listener, and the DB artifact failed insert validation on an invalid array
  handle ABI. Therefore no fresh nginx/PostgreSQL/SQLite parity row or CUDA
  acceleration row is admitted. Historical non-equivalent DB timings remain
  diagnostic only, and the missing runtime owners are recorded as a bug.
