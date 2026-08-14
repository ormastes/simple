# Feature: SimpleOS server execution matrix

## Raw Request

Build and verify filesystem-launched SimpleOS web/database servers on ARM64
QEMU and physical UNO Q, with separate CPU-only and GPU-accelerated UNO Q
evidence, parallel implementation lanes, guide/manual updates, and
highest-capability review. Compare the Linux Simple servers with nginx,
PostgreSQL, and SQLite without weakening architecture or making GPU/dynload
mandatory.

## Task Type

feature (with tracked ARM runtime, UNO Q toolchain, and Linux runtime bugs)

## Goal

Prove filesystem-backed web and database server executables on ARM64 QEMU and
the physical Arduino UNO Q QRB2210, including separate CPU-only and
GPU-accelerated UNO Q runs.

## Refined Goal

Ship real current-source filesystem-resolved web/database executables for
ARM64 SimpleOS under QEMU and physical UNO Q, prove persistence and separate
CPU/GPU execution with provenance-bound receipts, and retain fair Linux
comparison evidence without substitutes or architectural shortcuts.

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
- [ ] AC-16: Every implementation bug is claimed under `doc/08_tracking/bug`
  before edits, contains the exact pre-fix reproducer, names the Pure-Simple or
  kernel owner, covers one adjacent root cause, and permits runtime/C changes
  only with recorded boundary evidence.
- [ ] AC-17: Executable SSpec scenarios and mirrored operator manuals retain
  ARM blocked/PASS, UNO CPU, UNO GPU, Linux CPU, and Linux optional-GPU rows;
  missing helpers fail explicitly and no unavailable row is skipped.
- [ ] AC-18: Knowledge is current in requirements, architecture, design, plans,
  `doc/07_guide`, feature expert
  `doc/00_llm_process/feature_expert/simpleos_server_execution_matrix/skill.md`,
  layer expert `doc/00_llm_process/layer_expert/simpleos_platform/skill.md`, and
  every unresolved bug record. Workflow skill/agent/command files are N/A
  unless their behavior changes; generated/manual specs remain mandatory.
- [ ] AC-19: Any unavailable physical or native row retains an open Todo/resume
  plan naming owner, prerequisite, exact command, artifacts and final reviewer;
  an implementation handoff never closes the umbrella feature.

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

## Scope Exclusions

- No host, x86, marker, Linux-userspace, or Rust-seed result may substitute for
  a target SimpleOS executable receipt.
- No firmware flashing, repartitioning, boot-chain overwrite, or destructive
  physical-board mutation is authorized.
- CUDA/Vulkan is not added to socket, authentication, persistence, or
  filesystem ownership merely to create a GPU benchmark.

## Cooperative Review

- Sidecars: ARM64 network/syscall owner; ARM64 server/VFS/durability owner;
  UNO Q runtime/toolchain/board owner; Linux performance owner when runnable.
- Merge owner: root agent. Final reviewer: independent highest-capability agent.
- Shared interface: `SimpleOsServerExecutionReceiptV1`; modes and frozen
  `step("...")`/helper names are listed above.
- Setup/checker owners: `arm_qemu_server_fixture`, `uno_q_server_fixture` and
  the canonical QEMU/UNO evidence wrappers. Missing helpers use `fail(...)`.
- Generated-manual review owner: final highest-capability reviewer.

## Phase

implementation-active

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
- dev: ARM source now includes a current-source filesystem payload, modern
  VirtIO-MMIO NIC queues, TTBR0-aware bounded copy, capability-gated direct
  socket dispatch, FAT32 metadata sync, and negotiated VirtIO block FLUSH.
  These are static implementation prerequisites only; no ARM execution row is
  credited.
- dev-blocked: Canonical database atomic persistence still depends on hosted
  runtime file/process/time/liveness owners, while FAT32 replacement rename is
  non-atomic. The server therefore fails closed before listener publication.
  Host storage also remains below the 5 GiB execution admission floor and the
  ARM sysroot/runtime payload prerequisites are absent, so build/QEMU/reboot
  checks were not run. AC-1..3 and AC-10 remain open.
- verify-failed: The final static cycle found that ARM file open/write still
  recopies through unavailable `rt_copy_user_byte`, read copyout uses the
  generic VMM path, raw paths are capability-checked before normalization
  (allowing traversal outside an exact grant), and close can use a stale active
  FD context. The deliberate-red matrix fixtures also remain unimplemented.
  No normal commit/push is authorized; AC-1..3/9..11 remain open.
- build-blocked: A cache-preserving current-source compiler build stopped after
  two fail-fast cycles. Cycle 1 fixed one async `env_get` namespace drift;
  cycle 2 exposed broader unresolved module `GlobalLoad` owners and attempted
  forbidden stub fallback. No admissible compiler, ARM sysroot, or target
  runtime was produced; the retained native cache was preserved.
- dev: The canonical ARM sysroot builder now produces crt0, libc/C-runtime
  archive, compiler wrapper, and linker script. The archive is explicitly
  partial because the pure-Simple core target objects and
  `build/os/simple-core-simpleos-aarch64/libsimple_runtime.a` remain absent;
  this does not authorize a payload build or QEMU acceptance run.
- build-blocked: Final permitted cached compiler cycle 3 exited 1 after 4m40s
  with the same file-system namespace `GlobalLoad` failures, two existing
  `proof_uses` inference failures, and one frontend timeout. The source fix is
  bootstrap-circular when evaluated by the older Stage-2 compiler; forbidden
  stub fallback was rejected and no candidate executable was produced. No
  further compiler retry is allowed in this session.
- build-blocked: A single explicitly diagnostic ARM server payload build using
  the existing pure-Simple Stage-2 reached `ld.lld` and failed on five retained
  owner categories: `rt_array_enumerate`, `rt_file_rename`, unqualified
  `bytes_to_string`, `rt_arm64_syscall`, and `rt_unwrap_or_trap`. Objects remain
  under `.simple/native-objects-jWARot`; no executable or acceptance credit was
  produced.
- dev: Final payload-link cycle 3 resolved the retained symbol categories and
  produced a static AArch64 ELF from 57 current server/source modules with zero
  compile failures: `build/os/arm64_servers/servers.elf`, SHA-256
  `33c9dc640e3aa1a031de68d22869ba7867a14cd174966cf875fc596bd19fd481`.
  The builder is the older pure-Simple Stage-2, so this is bootstrap diagnostic
  progress, not current-compiler or live QEMU acceptance evidence.
- verify-blocked: The 2026-08-14 ARM QEMU preflight now passes the 5 GiB storage
  floor (1,195,233,558,528 bytes available) and finds
  `/usr/bin/qemu-system-aarch64`, so the earlier storage/QEMU observations are
  stale. It still fails because no executable current-source Simple compiler,
  ARM64 sysroot objects/archive/wrapper/linker script, or target
  `libsimple_runtime.a` exists. An existing 8,288-byte AArch64 server ELF was
  hashed but is not admitted as a fresh current-source payload. Per the stop
  rule, no build or QEMU was attempted; HTTP/VirtIO-net and fresh-boot DB
  readback remain unverified. Exact receipt:
  `doc/09_report/verify/simpleos_arm64_server_qemu_preflight_2026-08-14.md`.
- dev-blocked: QRB2210/Imola has no repository or public vendor contract for a
  SimpleOS signed boot bundle, partition/download manifest, rollback policy,
  factory recovery, or rootfs carrier. The frozen receipt retains
  `image_sha256` as non-sensitive provenance; credential-bearing image bytes,
  paths, and access details remain sensitive and non-distributable. The board
  remains read-only under `/tmp/unoq-server-matrix.lock`, and Debian receives no
  SimpleOS credit. Resume from TODO 808 and the signed-boot-owner bug only after
  authoritative Arduino/Qualcomm inputs exist.
- verify-blocked: Final cycle-3 review accepts this tree only as an honest WARN
  checkpoint. ARM network, file-boundary, target-runtime, payload, Recoverable
  Replace V1, crash-matrix, and credential-cleanup source owners are present,
  but the pre-QEMU capability probe still calls the mounted-state FAT accessor
  before those globals are published. It therefore reports `ready=false` and
  stops before QEMU. The crash-marker matcher is also not line-anchored, and
  target immutable-text zeroization remains unproved. The three-fix-cycle cap
  is exhausted: no ARM/UNO acceptance row or release gate is credited.
- dev: The next continuation corrected the pre-QEMU capability boundary. The
  offline structural check now validates the exact 512-byte SARD descriptor,
  256 MiB geometry, reserved-sector extent, and CRC/field corruption cases;
  production continues to consume only mount/recovery-published FAT truth.
  Independent highest-capability static review passed this boundary. QEMU is
  still blocked because no current-source Stage-4/full compiler or matching
  `simpleos-arm64-current-source-compiler-admission-v1` receipt exists.
- verify-blocked: A fresh read-only UNO Q audit finds the Arduino Imola device
  connected but still running vendor Debian, with no authoritative QRB2210
  signed SimpleOS bundle, partition/download and rollback manifest, recovery
  procedure, rootfs/runtime, or evidence provider. CPU and GPU acceptance rows
  remain open; the board was not mutated.
- dev: Added and highest-capability-reviewed the fail-closed Stage-4 compiler
  admission producer `scripts/check/admit-simpleos-arm64-server-compiler.shs`.
  It verifies canonical provenance and essential tools, builds and hashes the
  real ARM payload with target sysroot/runtime/linker/no-stub policy, binds the
  exact dirty-inclusive QEMU manifest, rejects traversal/symlink outputs, and
  publishes a mode-0600 receipt only as the final atomic action. Negative-only
  self-tests cannot fabricate admission. No Stage-4 compiler exists yet, so no
  receipt or QEMU evidence was produced.
- verify-blocked-unoq-final-20260814T081152Z: The canonical wrapper retained its
  exact producer snapshot, acquired the UNO lock, captured every command stream
  and exit, derived validated GPU fields, and atomically published the final
  receipt. CPU runner `scripts/check/run-unoq-qrb2210-cpu-server-live.shs` is
  absent (`test -x` exit 1); GPU exited 2 at `pure-simple-runtime-missing`.
  Receipt SHA is `718ddcde...efdb93d`, manifest SHA is
  `7bf25984...10bcbed`, and the single checksum verification passed all entries.
  CPU/GPU remain BLOCKED; no provider execution, board mutation, download,
  boot change, commit, or push occurred.
- dev-unoq-cpu-runner: Added the missing canonical CPU live runner and focused
  negative-only shell contract/manual. The runner gates all board access on the
  current-source compiler admission, source manifest, and exact AArch64 ELF;
  rejects Debian; requires signed boot/recovery identity; and validates forced
  CPU, accelerator non-selection, HTTP bytes, authenticated DB fresh-reboot
  persistence, credential destruction, and parent-authoritative pointer-free
  receipt fields. The negative self-test passed once and did not access ADB.
  No live board run, mutation, download, commit, or push occurred; CPU remains
  BLOCKED pending admitted artifacts and physical SimpleOS QRB2210 boot.
- dev-unoq-cpu-runner-cycle2: Aligned admission parsing with emitted
  `native_smoke_output_sha256`/`source_revision` semantics; bound remote
  provenance, signed bundle, provider, and compiler-admission hashes; enforced
  lowercase SHA-256 and cross-field HTTP/DB equality; required distinct reboot
  IDs; and added host-observed maps/fds, pre/post binary hashes, cleanup, atomic
  output, and validated inherited-lock-FD ownership. Negative sabotage covers
  Debian, GPU selection, malformed/mismatched hashes, duplicate fields, missing
  reboot, and retained credential matches. The focused negative contract passed
  once before the final lock/maps hardening; those final source-only additions
  were not rerun to avoid repeating the session's one static contract. No ADB,
  board, commit, or push action occurred.
- verify-blocked-qemu-20260814T080211Z: The canonical ARM server gate ran once
  at HEAD `900f9188ac50182f8f95505639072e9b1d9f7e2e` with both compiler admission
  variables explicitly unset. It exited 1 at the mandatory missing
  `SIMPLE_BUILD_COMPILER` check before payload build, image creation, or QEMU.
  Retained stdout/stderr/state hashes passed independent review. No Stage-2,
  Rust-seed, stale-ELF, x86, or marker substitution occurred; AC-1..3 remain
  open pending a provenance-admitted current-source Stage-4/full compiler.
- dev-unoq-cpu-runner-cycle3: Collector summaries now derive from validated
  runner output; inherited FD9 retains the real flock; pre/post PIDs bind exe,
  forced-CPU cmdline, maps, and fds; and host-owned HTTP, DB/reboot, credential,
  cleanup, and atomic-output observations replace provider self-assertions.
  Static cycle 1 failed only on a stale cleanup marker, diagnostic cycle 2
  localized it, and final cycle 3 passed. No ADB/live board, mutation, download,
  commit, or push occurred.
- verify-blocked-unoq-cpu-runner-cycle3: Independent final review rejected the
  runner as acceptance evidence. Blocked exits can still publish false
  no-mutation summaries; cleanup is incomplete; credential scanning is
  provider-selected; HTTP and DB responses are not parsed exactly; signed-boot
  identity lacks a locally trusted manifest; and collector producer, exit, and
  collision evidence remain incomplete. The three-cycle cap is exhausted, so
  AC-4..8 remain open and no physical run is authorized.
- build-blocked-stage3-lifecycle-cycle3: Reused HirLowering ownership and
  in-place transient reset are present across the known module loops, and the
  false runtime-object-count memory oracle was removed. The static gate was not
  rerun after its final anchor correction, and no current full CLI can execute
  the behavioral spec. Nested collection backing allocation, no-GC retention,
  and representative Stage3 RSS remain unproved; the P0 bug stays OPEN.
