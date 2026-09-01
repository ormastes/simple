# Simple NVMe SSD Firmware Hardening, Controller-Portability, and Verification Plan

**Repository audited:** `ormastes/simple`
**Audited revision:** `0fce018eda368724ab9650aa8af1207c3f9179ce`
**Revision date:** 2026-08-27 UTC
**Research date:** 2026-08-28 KST
**Document status:** Architecture decision and implementation plan
**Primary scope:** `examples/09_embedded/simpleos_nvme_fw`, its RV32 firmware path, associated FPGA/RTL test paths, and the Simple compiler/runtime features needed to harden them

---

## 1. Executive decision

The current Simple NVMe firmware work should **not** be generalized by adding more controller-specific conditionals to the existing example. It should be split into a reusable, statically profiled firmware product and a thin example/board entry layer.

The target is:

> A fully typed, fixed-capacity, asynchronous NVMe SSD firmware core that supports every **documented and certified controller/media profile**, while making direct or illegal NAND, emulator-memory, MMIO, DMA-descriptor, allocator-backing-store, and test-hook access mechanically impossible or independently detectable.

"Support all controllers" cannot honestly mean every commercial SSD controller. Most commercial controller register maps, NAND PHY interfaces, firmware ABIs, ROM protocols, and security boot chains are private. In this plan it means:

> Every controller for which a complete `ControllerProfile`, compatible `MediaProfile`, board support package, and conformance evidence bundle exists.

A controller is not considered supported because the source compiles. Certification has levels:

| Level | Meaning |
|---|---|
| C0 — Schema | Profile parses, validates, and generates code. |
| C1 — Build | Firmware statically compiles and links for the target. |
| C2 — Model | Host/reference and controller-model tests pass. |
| C3 — RTL/co-simulation | Firmware-in-loop, bus assertions, reset, and DMA tests pass. |
| C4 — Transport HIL | A host enumerates the endpoint and passes destructive NVMe conformance on hardware. |
| C5 — Real media HIL | Real NAND discovery, read/program/erase, ECC, bad-block, read-retry, and recovery pass. |
| C6 — Production evidence | Power-cut, endurance, fault containment, security, reproducibility, and release gates pass. |

The first profiles should be:

1. **`SimpleFpgaRv32`** — preserves the current in-repository RV32/AXI/GHDL path as the first portability target.
2. **`CosmosPlusZynq7000`** — first concrete open research board with real NAND channels.
3. **`LinuxPciEndpointReference`** — transport portability reference, based on Linux PCI endpoint-controller concepts; not a hard-real-time NAND target.
4. **`HostReference`** — strict deterministic model used as the semantic oracle.
5. **`FemuDifferential` and `NvmeVirtDifferential`** — external differential-test targets, explicitly not production controller profiles.

The most important hardening decision is the user's clarification:

> **AOP is the verifier and policy-enforcement layer. It is not the NAND abstraction.**

The NAND abstraction is an opaque typed service. AOP proves that all code uses that service and that no alternative path exists.

---

## 2. Non-negotiable invariants

The following invariants define completion. A build that violates any production invariant must fail closed.

### 2.1 Access invariants

1. FTL, reliability, NVMe, and scheduling code cannot read or write NAND-emulator storage arrays.
2. Production code cannot import, name, reflect over, relocate to, or dynamically resolve test/emulator internals.
3. Only the controller BSP may touch controller MMIO registers.
4. Only the DMA service may create or mutate DMA descriptors, IOVA/physical addresses, PRP walkers, and cache-maintenance sequences.
5. Only the media service may issue NAND bus/FMC/PHY operations.
6. Only allocator implementations may touch arena backing storage, free maps, generation tables, or poison metadata.
7. A raw address, pointer cast, inline assembly access, or foreign-function escape is forbidden unless it is inside an explicitly reviewed `unsafe` hardware-boundary module and appears in the generated access manifest.
8. Every external effect is classified by capability and appears in an artifact-bound proof receipt.

### 2.2 Type invariants

1. A logical block address is not interchangeable with a physical page number.
2. A queue ID is not interchangeable with a command ID or queue slot.
3. A NAND channel/way/LUN/plane/block/wordline/page coordinate is profile-bound and range checked.
4. A DMA length is not interchangeable with a block count or byte offset.
5. A handle from one pool, generation, object kind, controller, namespace, or ownership domain cannot be used in another.
6. Wire-format integers are decoded once into semantic types; business logic does not repeatedly manipulate unvalidated command dwords.
7. Runtime-discovered NAND geometry may narrow compile-time maxima but may never silently exceed generated capacities.

### 2.3 Embedded-runtime invariants

1. No heap allocation occurs in the firmware hot path or hard-real-time mode.
2. No closure capture, callback list, recursive promise chain, or unbounded continuation exists on device.
3. Every async operation has a statically bounded state machine and pool.
4. Every ring operation has bounded retry or explicit backpressure.
5. Every task has an owner, priority class, deadline policy, cancellation policy, and maximum retained resources.
6. ISRs acknowledge hardware and enqueue typed events; they do not execute FTL policy or wait.
7. Resource admission happens before an operation can partially mutate durable state.

### 2.4 Evidence invariants

1. A PASS string alone is not evidence.
2. Every test result binds source revision, compiler binary/hash, profile hash, generated code hash, AOP policy hash, linker map, firmware image hash, test vector, and tool versions.
3. Reference model and implementation are independently constructed where feasible.
4. Production images contain zero emulator/test/fake/mock symbols or data sections.
5. Every negative access test passes only when the compiler, linker, verifier, or hardware protection mechanism rejects or traps the illegal operation.

---

## 3. Research method and evidence grading

This report distinguishes four classes of evidence:

| Grade | Evidence | Permitted claim |
|---|---|---|
| A | Real controller + real host + real NAND + destructive/recovery/power tests | Hardware/media behavior demonstrated for that exact profile. |
| B | Synthesizable RTL or endpoint HIL + firmware-in-loop + independent host tests | Transport/controller behavior demonstrated; not real-NAND proof. |
| C | Full-system emulator or deterministic software model + differential tests | Semantic or timing-model evidence; not hardware proof. |
| D | Self-test, static marker, source inspection, or documentation only | Useful development evidence; no hardware or durability claim. |

The current Simple tree contains meaningful B/C/D evidence, but no basis to claim C5/C6 real-media production readiness.

The open-source survey also separates two kinds of "automation" that are often confused:

- **Data-path automation:** hardware or firmware offload of NVMe queue fetch, PRP/SGL traversal, DMA, completion posting, NAND scheduling, ECC, and interrupts.
- **Engineering automation:** reproducible builds, CI matrices, simulation, lint, formal checks, synthesis, host conformance, HIL orchestration, artifact manifests, and release evidence.

A project can have excellent hardware automation and weak CI, or excellent CI while being only an emulator.

---

## 4. Current Simple NVMe SSD firmware status

### 4.1 Audited implementation lanes

The repository currently contains several related but materially different lanes. They must not be described as one production firmware implementation.

#### Lane A — Host-runnable firmware/reference stack

Path:

```text
examples/09_embedded/simpleos_nvme_fw/fw/
```

This is the broadest implementation. It contains NVMe command handling, FTL and mapping logic, a Flash Interface Layer, ECC and bad-block handling, reliability/read-retry work, fault injection, object-pool work, and many self-tests. It is valuable as an executable reference and algorithm workbench.

It is not presently a deployable controller-neutral firmware image because:

- it constructs dynamic arrays for media and metadata;
- many semantic values are plain `i64`;
- test and emulator controls are exposed through production-facing structures;
- backend selection is represented inside shared objects;
- internal arrays are structurally accessible;
- the page model can use one `i64` as a stand-in for a 4 KiB page;
- the standard Promise implementation is dynamic and host-oriented;
- access boundaries are conventions rather than end-to-end verified facts.

#### Lane B — RV32 scalar firmware floor

Path:

```text
examples/09_embedded/simpleos_nvme_fw/fw_rv32/
```

This lane demonstrates that selected firmware logic can be built into a bare-metal RV32 ELF and exercised under QEMU/GHDL/FPGA-oriented flows. It is useful and should be preserved as a portability profile.

It is not a complete no-allocation port of Lane A. The build script currently performs substantial source flattening, collision checking, and broad text transformations such as `i32` to `i64` conversion for selected paths. That is a bootstrap/workaround mechanism, not the desired module/profile compilation architecture.

#### Lane C — Minimal RV32 NVMe/AXI endpoint and SoC RTL

Key paths:

```text
examples/09_embedded/fpga_riscv/rtl/rv32_nvme_axi.vhd
examples/09_embedded/fpga_riscv/rtl/tb_rv32_nvme_fw_in_loop.vhd
examples/09_embedded/fpga_riscv/rtl/tb_rv32_nvme_host_axi_mmio.vhd
```

This is a useful minimal endpoint/controller model. At the audited revision it is intentionally constrained: a small queue set, one command/transaction style, 32-bit-oriented transport assumptions, small queue depths, and a command subset. It should become the `SimpleFpgaRv32` profile rather than leaking its register layout or queue assumptions into the FTL.

It does not yet constitute a complete SSD controller with a real NAND controller/PHY, full DMA engine, production reset/interrupt behavior, or power-loss model.

#### Lane D — Teaching/demo wrappers

Files such as the top-level example and pool demonstrations are educational entry points. They should remain, but the production core should move out of `examples/` so a teaching simplification cannot accidentally become a release implementation.

### 4.2 What is already strong and should be retained

The current work is not a blank slate. Several components are worth preserving:

1. **Layering intent:** NVMe → FTL → FIL → FMC/NAND is visible in the design.
2. **Fault-oriented testing:** program/erase/read faults, recovery, refresh, remap, and retention-oriented tests already exist.
3. **Generation handles:** `fw_pool.spl` uses a generation-stamped fixed pool to detect stale handles.
4. **Firmware-in-loop automation:** GHDL runs actual RV32 firmware against the RTL model.
5. **Source-matched evidence:** the recovery script records revision, compiler and image hashes, RTL/source hashes, and simulation logs.
6. **Multiple execution environments:** host model, QEMU, GHDL, BRAM/AXI paths, and optional FPGA/JTAG flows are present.
7. **Fail-closed test harness behavior:** several scripts reject missing markers, duplicate markers, invalid ELF properties, or failed tools rather than silently skipping.
8. **AOP architecture-rule foundation:** the language already documents compile-time `forbid`/`allow` dependency rules and execution pointcuts.

These are foundations to harden, not reasons to preserve current cross-layer visibility.

### 4.3 Critical current boundary violations

#### P0-1 — Raw `.nandram` access in firmware-in-loop tests

The current GHDL firmware-in-loop script extracts `_nandram_start` and `_nandram_end` from the ELF, requires a specific section size, computes a raw word offset, and supplies it to the VHDL testbench. The testbench then directly writes/reads offsets within that state to inject faults and inspect recovery counters.

The QEMU host-parity script likewise attaches through GDB and directly reads/writes `.nandram` addresses, including programmed data, retention/fault fields, and recovery counters.

This is exactly the bypass the new AOP policy must reject. It is useful historical white-box evidence, but it must be replaced by an explicit test-control port and immutable observability interface.

#### P0-2 — Emulator/media state is structurally public

`NandDevice` publishes arrays such as `page_data`, OOB arrays, error arrays, programmed bits, bad-block state, erase counters, and fault-arm arrays as struct fields. Any code that receives the object can bypass the intended protocol and mutate storage directly.

A naming rule or review convention cannot secure this. The representation must be private/opaque, and the compiler must prove that no external load/store reaches its storage region.

#### P0-3 — Test and emulator controls share production-facing objects

`Fmc` contains both a behavioral `NandDevice` and an optional `NandEmu`. The emulator constructor still builds the behavioral device, and `Fmc` exposes sideband fault injection, corruption, time advancement, wear setting, Vref setting, histograms, and margins. Some emulator-only methods become silent no-ops or empty/zero results on the default backend.

This creates three failure modes:

- a test-only control can be called by production logic;
- an unsupported operation can appear successful because it is a no-op;
- both backends and their state can remain linked into an image.

The target design uses separate statically selected binaries and capabilities. A production real-NAND profile cannot name or link emulator APIs.

#### P0-4 — AOP currently verifies dependencies, not all memory effects

Current AOP architecture rules can forbid imports/dependencies and weave call advice. That is necessary but insufficient. A helper, generic instantiation, macro expansion, FFI call, raw cast, inline assembly block, or direct load/store can bypass a call-only rule.

The compiler needs typed HIR/MIR pointcuts and a post-lowering access receipt covering every memory and external effect.

#### P0-5 — Current Promise is not the embedded Promise

The standard Promise implementation uses dynamic classes, callback collections, closures, and general host-runtime behavior. Reusing it directly in firmware would violate fixed-memory and bounded-execution requirements.

A distinct `std.embedded.async` Promise/Future model is required. It may share surface syntax and lowering concepts, but its runtime representation must be fixed-slot, closure-free, and profile-bounded.

### 4.4 High-priority correctness and maintainability gaps

#### P1-1 — Semantic values remain raw `i64`

The repository has begun wrapping NAND coordinates (`NdChannel`, `NdWay`, `NdBlock`, and related types), but many constructors, fields, conversions, task slots, opcodes, statuses, capacities, and addresses remain `i64`. Public task-pool arrays hold command IDs, LBAs, block counts, physical pages, phases, sequence numbers, and statuses without type separation.

This permits valid-range but semantically invalid substitutions.

#### P1-2 — Pool backing arrays remain externally reachable

`TaskPool` uses a useful generation check, yet all generation, used-bit, command, LBA, phase, PPN, sequence, status, capacity, and live-count arrays are fields on the public struct. A caller can forge pool state without using `acquire`, `valid`, or `release`.

#### P1-3 — Generation saturation is not a complete wrap policy

The current generation increment saturates at a safe integer limit, after which a slot is effectively unavailable. This is safer than wrapping, but the policy is implicit and not tied to pool health telemetry, capacity-reserve rules, or a formal proof that the remaining pool can satisfy hard-real-time admission.

The target allocator explicitly retires near-wrap slots, reports retirement, and proves a minimum permanent reserve.

#### P1-4 — Media fidelity is mixed

The ONFI-shaped model drives command/address/data/status sequences, but one `i64` can represent the main page payload. The Vt/physics model is useful for reliability experiments, but reduced geometry and aliasing cannot be represented as full-device proof.

Models must be labeled by fidelity tier, and a one-word page must never satisfy a "real page/OOB/ECC" acceptance gate.

#### P1-5 — Documentation and code can drift

Some module commentary describes the Vt backend as not wired or describes older limitations while current composition code contains an emulator constructor and dispatch seam. Documentation generated from profiles, tests, and build receipts should replace hand-maintained claims where possible.

#### P1-6 — Current endpoint assumptions are not isolated as a profile

Queue count, queue depth, address width, mailbox locations, memory regions, entry addresses, and firmware section sizes appear in scripts/testbenches. They need one generated profile source of truth.

### 4.5 Existing automation: value and limitations

| Existing automation | Current value | Hardening limitation |
|---|---|---|
| RV32 bare-metal build | Demonstrates compiler/backend/link path. | Source flattening and textual transforms are too fragile for profile certification. |
| QEMU boot script | Validates ELF shape, boot marker, fail behavior; harness has self-tests. | The harness self-test intentionally uses fake QEMU/readelf; it must remain test-infrastructure-only and never count as firmware execution evidence. |
| QEMU host-parity script | Sends host-like commands and checks write/recovery behavior. | Injects and inspects state by direct GDB `.nandram` access. |
| GHDL firmware-in-loop | Runs the real RV32 image with RTL. | Testbench relies on raw NAND state offsets; limited endpoint/controller behavior. |
| Recovery script | Binds source/compiler/image/RTL hashes and runs clean/garbage cases. | Marker-centric result semantics; no independent media oracle or AOP access receipt. |
| Optional KV260/JTAG flow | Provides hardware-oriented execution evidence. | Does not prove real PCIe endpoint behavior or real NAND media behavior. |
| Host firmware self-tests | Broad algorithm and fault coverage. | Same implementation may construct both implementation and oracle; dynamic/reference model only. |

The correct migration strategy is to retain these paths as baseline tests while replacing their illegal observation mechanism and raising their evidence grade.

---

## 5. Open-source SSD firmware/controller landscape

### 5.1 Classification rules

A project is counted as **real NAND-capable firmware** only when it has code for a concrete NAND controller/media path or an open-channel device path. An NVMe endpoint backed by DRAM, a Linux block device, a file, or a host-attached SSD is useful but not real NAND firmware.

A project is counted as an **NVMe device frontend** when it implements endpoint-side NVMe queue/controller behavior but leaves media/FTL elsewhere.

A project is counted as a **test oracle** when it is an emulator, simulator, virtual kernel device, host test driver, or conformance suite.

An FPGA design in which the FPGA is the PCIe root/host controlling a commercial NVMe drive is **not** an SSD device controller and must not appear in the supported-device profile list.

### 5.2 Survey matrix

| Project | Class | Concrete controller/platform support | Media support | Data-path automation | Engineering automation observed | Use in Simple plan |
|---|---|---|---|---|---|---|
| **Cosmos+ OpenSSD** | Real NAND research SSD | Cosmos+ board; Xilinx Zynq-7000-class SoC/FPGA platform; multi-channel NAND controller | Real raw NAND on the board | Firmware/FPGA NAND scheduling, ECC/controller logic, NVMe path | Xilinx project/SDK, JTAG/UART, tutorials; canonical repository has little modern CI | First real-NAND profile and register/scheduler reference. Do not copy into the core without license/SPDX review. |
| **Jasmine OpenSSD** | Legacy real NAND SSD | Jasmine board with Indilinx Barefoot controller; SATA generation | Real NAND | Firmware FTL/NAND command path | GNU Makefile, ARM RVDS batch builds, several FTL variants; no modern CI observed | Legacy NAND/FTL and failure-handling reference only; not an NVMe profile. |
| **`freshLiver/ocp-fw`** | Cosmos+ firmware fork | Cosmos+ board/Toshiba-oriented configuration | Real NAND | Firmware FTL/controller path | GitHub Actions installs ARM cross-toolchain and runs `make all`; docs deployment workflow | Reproducible cross-build pattern and Cosmos+ bring-up reference. Its CI is build-level, not comprehensive HIL proof. |
| **OCSSD-plus** | Open-channel SSD on Cosmos+ | Cosmos+ hardware | Raw/open-channel NAND exposure | Open-channel data path | Vendor/Xilinx-oriented project, sparse canonical automation | Open-channel profile semantics and host-managed-media experiments. |
| **OX controller** | SSD controller/FTL framework | DFC open-channel SSD; Broadcom Stingray ARM; x86; software/file/DRAM modes | Open-channel media, DRAM/VOLT, file backend; block FTL with mapping/GC/WAL/checkpoint/recovery | Media-manager and FTL plug-in architecture; NVMe PCI/NVMe-oF paths | CMake, local throughput/read/write/admin tools, runtime statistics and BBT tasks; no GitHub Actions observed in the audited tree | Best architectural precedent for separating media manager, FTL, transport, and test backends. Linux/user-space assumptions must not enter hard-real-time core. |
| **NVMe CSD** | Portable Linux NVMe endpoint firmware | Tested on ZCU106, RK3399 boards, RK3588 boards, and BeagleY-AI/AM67A; extensible where Linux PCI endpoint-controller driver exists | Arbitrary Linux block backend; may be SATA/USB/RAM/etc., not intrinsic NAND | Linux PCI endpoint function, DMA/threads, custom compute commands | Per-platform kernel/rootfs/device-tree build instructions and runtime launch script | Transport HAL and capability-profile precedent. It is not evidence of real NAND firmware portability. |
| **OpenExpress** | Hardware NVMe device frontend | FPGA research platform from the published project | External/custom backend; frontend-focused | Fully hardware-automated queue request processing, concurrency, SQ/CQ management; reported near-PCIe-limit throughput | Research/Vivado project availability; automation is mainly datapath hardware, not a broad CI matrix | Queue/PRP/completion offload architecture reference; not the FTL/media layer. Treat repository licensing separately from paper availability. |
| **NVMeCHA** | Hardware NVMe device frontend | Xilinx KCU105, PCIe Gen3 x8, Vivado/Vitis 2019.2 | Frontend/controller test memory rather than a complete NAND SSD stack | One software-assisted admin controller plus parallel hardware-automated I/O controllers, one per queue pair | Vendor project setup; no broad modern CI observed | Optional high-throughput frontend profile/reference after core correctness. Not a real NAND profile. |
| **Lambda-IO** | Computational-storage stack and OpenExpress-derived controller | Daisy/DaisyPlus OpenSSD platforms | Computational-storage backend | Refactored OpenExpress controller plus device/host execution stack | Root CMake and component CMake/Makefiles; host/cross-compile modes | Reference for separating reusable controller frontend from computational functions. |
| **PNVMe** | DRAM-backed FPGA NVMe endpoint | Artix-7 board with onboard DDR3 | DDR3, not NAND | Custom XDMA/NVMe harness | Project-level build/test instructions | Small endpoint smoke/profile reference only; must be labeled non-NAND. |
| **FEMU** | Full-system NVMe SSD emulator | QEMU/KVM x86 host | DRAM/file model; BlackBox, Open-Channel, ZNS, NoSSD, CSD modes | Software model | GitHub Actions across Ubuntu 20.04/22.04/24.04; builds, device/mode instantiation, config checks, quality checks, artifacts | Primary external differential and fault/timing oracle. Never linked into firmware. |
| **NVMeVirt** | Linux kernel virtual NVMe device | Linux kernel module | Reserved host memory; conventional/NVM/ZNS/KV modes | Kernel threads and PCI-layer virtual device | Kbuild/Make, manual target selection, separate evaluation repository; no native CI observed | Independent host-visible behavior and performance differential target. |
| **SimpleSSD FullSystem** | gem5 SSD simulator | gem5 full-system platforms | Configurable SSD/NAND timing/model | Event-driven simulation | SCons, GoogleTest unit tests, tagged system tests, parallel/rerun test infrastructure; no project-specific GitHub Actions observed | Performance/timing and workload-model comparison. |
| **pynvme** | Host-side NVMe validation framework | Multiple physical/emulated NVMe controllers/namespaces | Whatever device under test provides | User-space access to PCI config/BAR, arbitrary commands, MSI/MSI-X, workloads, checksums | Pytest integration | Main programmable host conformance/fuzz/HIL harness. |
| **Linux blktests** | Kernel block/NVMe regression suite | Linux-visible block/NVMe devices | Device under test | Host/kernel test framework | Reusable shell test framework, NVMe and block groups, fio/nvme-cli integration | Mandatory destructive transport/HIL regression gate. |
| **OpenFlash Controller Lab** | Early architecture laboratory | Simulator/QEMU/driver scaffolding; roadmap to FPGA | Behavioral model | Controller, queue ABI, FTL and scheduler model | CI-pinned QEMU integration and tests according to project documentation | Monitor as a young reference; do not treat as mature firmware or hardware evidence. |

### 5.3 Explicit non-targets

The following kinds of projects should not be counted as SSD firmware controller support:

- **LiteNVMe**, `mcrl/NVMe`, FastPath-style FPGA NVMe initiators, or FPGA Drive designs where the FPGA is the host/root complex controlling a commercial NVMe SSD.
- Host NVMe drivers and SPDK initiators.
- QEMU NVMe devices without a deployable firmware/controller path.
- DRAM-backed endpoint demonstrations when discussing real NAND support.
- A commercial controller named in a datasheet when its firmware interface/register map is not available.

They remain useful for host traffic generation, link validation, or comparative architecture work.

### 5.4 Reuse decision

The Simple implementation should reuse **ideas and test vectors** more aggressively than source code.

| Source | Reuse |
|---|---|
| Cosmos+/Jasmine | NAND command sequences, controller-driver partition, scheduling and recovery cases, board bring-up knowledge. |
| OX | Media-manager/FTL/transport separation, checkpoint/recovery test cases, admin diagnostics. |
| OpenExpress/NVMeCHA | Queue/DMA/completion offload decomposition and performance counters. |
| NVMe CSD | Machine-readable transport capabilities and Linux endpoint portability model. |
| FEMU/NVMeVirt/SimpleSSD | Differential behavior, workloads, fault/timing cases. |
| pynvme/blktests/nvme-cli/SPDK | Host conformance, malformed-command tests, reset/error paths, performance validation. |

Before copying any implementation code, run an SPDX/license compatibility review and maintain a source-origin ledger. The default plan is independent reimplementation from public specifications and observed architectural patterns.

---

## 6. Standards and compatibility baseline

### 6.1 NVMe

The protocol ceiling for new design work should be the current modular NVMe specification set rather than an old monolithic revision. As of the research date, NVM Express lists:

- NVMe Base 2.4;
- NVM Command Set 1.3;
- ZNS Command Set 1.5;
- Key Value Command Set 1.4;
- Subsystem Local Memory Command Set 1.3;
- Computational Programs Command Set 1.3;
- NVMe over PCIe Transport 1.4;
- NVMe over RDMA and TCP Transport 1.3;
- current Boot and Management Interface documents.

This is a **specification ceiling**, not an initial implementation promise. The first production profile should implement a deliberately small, correct NVM/PCIe subset with generated capability bits. Unsupported commands and features must be reported accurately; they must not be accepted as no-ops.

Recommended staged command-set scope:

| Stage | Required |
|---|---|
| P0 transport bring-up | Controller enable/disable/reset, admin SQ/CQ, Identify, Get Log Page minimum, Create/Delete I/O SQ/CQ, Abort basics, error log. |
| P1 block I/O | Read, Write, Flush, Write Zeroes if truly implemented, Dataset Management if truly implemented; PRP validation. |
| P2 robust operation | Multiple queues, MSI/MSI-X, namespace lifecycle policy, power-state/health reporting, firmware slot/update design, telemetry. |
| P3 extensions | SGL, ZNS, KV, computational programs, SR-IOV/virtualization, fabrics only as separately profiled modules. |

No Identify field may advertise a feature until its positive, negative, reset, fault, and persistence tests pass.

### 6.2 PCIe

PCIe 7.0 version 1.0 was released in 2025 at 128 GT/s. PCIe 8.0 remains a development target rather than a released production baseline. The firmware architecture should be transport-generation-neutral, but the initial controller profiles should match practical available hardware—likely Gen2/Gen3 for Cosmos+/research boards and whatever the Simple FPGA endpoint actually implements.

The profile must encode, rather than infer:

- generation and lane count;
- maximum payload/read-request size;
- address width and outbound/inbound windows;
- BAR layout and alignment;
- MSI/MSI-X capability and vector count;
- atomic/coherency behavior;
- DMA aperture and IOMMU assumptions;
- reset types and timing;
- surprise removal/link-down behavior;
- completion timeout and replay/error reporting;
- cache maintenance and ordering barriers.

### 6.3 NAND interface ceiling

Use ONFI 5.2 as a modeling ceiling where public documentation permits, with optional Toggle/vendor extensions in separate media profiles. Normative implementation must be checked against lawfully acquired current ONFI/JEDEC/vendor documents before claiming conformance.

The media profile and runtime discovery path must cover:

- manufacturer/device/parameter-page identification and CRC validation;
- channel, target, LUN, plane, block, wordline, page, and codeword geometry;
- page/OOB size and ECC layout;
- supported timing modes and training;
- command/address/data bus width;
- cache/multi-plane/copyback support only when safe and verified;
- bad-block marker location and factory-bad handling;
- read-retry feature set and vendor extensions;
- program order and partial-program restrictions;
- endurance and retention classes;
- suspend/resume and reset behavior;
- ready/busy and status semantics;
- power-fail constraints.

Runtime discovery can select a narrower `DiscoveredMedia` inside compile-time `MediaLimits`. It cannot allocate larger tables or rings than the compiled profile permits.

### 6.4 Machine-readable hardware descriptions

SystemRDL, IEEE 1685 IP-XACT, and CMSIS-SVD demonstrate the value of one register source generating RTL/software/documentation views. None alone covers all SSD profile semantics, so Simple should define a compact native schema with import/export adapters:

- import SystemRDL/IP-XACT/CMSIS-SVD register blocks where available;
- describe transport, DMA, interrupt, memory, security, NAND geometry, ECC, and timing in a Simple-specific profile schema;
- generate typed register accessors, RTL packages, C/Simple headers, linker fragments, AOP policy facts, testbench constants, docs, and conformance vectors from one source.

Generated files are never hand edited. CI regenerates them and fails on differences.

### 6.5 Hardware access containment

RISC-V PMP provides per-hart physical read/write/execute restrictions and precise traps. Smepmp adds stronger M-mode allowlist/lockdown behavior. Where available, the firmware should combine:

- compile-time AOP and typed-IR access verification;
- PMP/Smepmp or MPU regions;
- IOMMU/SMMU DMA apertures;
- FPGA AXI firewalls and bus assertions;
- controller-specific privilege and memory windows.

A declarative access manifest should play a role similar to a capability-distribution description: it states which component can ever access which resource and is checked both statically and during platform initialization.

---

## 7. Target product architecture

### 7.1 Product boundary

Move the reusable implementation out of the example tree. The example should select profiles and exercise public APIs; it should not own the core implementation.

Proposed high-level structure:

```text
src/firmware/nvme_ssd/
  spec/                  # NVMe and controller/media profile schemas
  generated/             # generated, never hand-edited
  core/
    types/
    effects/
    errors/
    state/
  runtime/
    embedded_async/
    rings/
    timers/
    alloc/
  transport/
    nvme/
    pcie/
  services/
    controller/
    dma/
    irq/
    media/
    telemetry/
    recovery/
  ftl/
    mapping/
    allocator/
    gc/
    wear/
    checkpoint/
    journal/
  reliability/
    ecc/
    retry/
    refresh/
    disturb/
    retention/
    raid_rain/
  profiles/
    controller/
    media/
    board/
  bsp/
    simple_fpga_rv32/
    cosmos_plus_zynq7000/
    linux_pci_endpoint_reference/
  verification/
    aop/
    formal/
    manifests/
  test_models/           # excluded from production dependency graph
    media_functional/
    media_timing/
    media_reliability/
    host_reference/
  tests/
    unit/
    property/
    negative_access/
    differential/
    rtl/
    hil/
  tools/
    profile_gen/
    evidence_pack/
    access_verify/

examples/09_embedded/simpleos_nvme_fw/
  README.md
  main.spl              # thin HostReference example
  profiles/             # example selections only
  demos/
```

The current files can move incrementally. Do not begin with a large rename that breaks every test; introduce the new modules, wrap old behavior, and migrate by vertical slice.

### 7.2 Layering

```text
Host / PCIe
    |
    v
NVMe PCIe transport
    |  decoded typed commands
    v
NVMe command service
    |  typed block operations
    v
I/O admission + async scheduler
    |
    +----> DMA service --------> Controller BSP / DMA engine
    |
    +----> FTL/reliability ----> Media service ----> Real NAND BSP
                                      |
                                      +-----------> Test model adapter (test binary only)
```

Cross-layer rules:

- NVMe code cannot see NAND coordinates.
- FTL cannot see MMIO registers or DMA descriptors.
- Media service cannot see host PRPs/SGLs.
- Controller BSP cannot decide mapping/GC policy.
- Emulator code cannot be imported by production modules.
- Telemetry observes immutable events; it cannot mutate subsystem state.

### 7.3 Static composition modes

#### Production static profile

One controller, one board, one media family/limit set, one command-set selection. Compile-time monomorphization removes unused branches. This is the default for embedded firmware.

#### Certified multi-board image

Optional image with a small boot-time board-ID dispatch among precompiled profiles that share an ABI and memory budget. Hot paths still use a sealed static dispatch table selected once. It is not a general plugin loader.

#### Host/reference image

May use dynamic plug-ins and rich diagnostics. It is explicitly not the production artifact and is built under a different dependency/AOP policy.

#### Test image

May include media models and fault-control capabilities. It carries a distinct build identity and cannot be signed as production firmware.

### 7.4 Controller/media independence

Controller and media are separate axes.

```text
ControllerProfile = CPU + memory map + PCIe/NVMe frontend + DMA + IRQ + clocks + reset + protection
MediaProfile      = NAND protocol + geometry limits + ECC + timing + retry + bad-block + power behavior
BoardProfile      = legal ControllerProfile × MediaProfile composition + wiring + power + clock constraints
```

A controller with only a Linux block backend is compatible with `BlockBackendMedia`, not automatically with `RawNandMedia`. A Cosmos+ NAND profile cannot be combined with an unrelated controller unless the BSP supplies the required channels, PHY, ECC, DMA, and timing capabilities.

### 7.5 Capability negotiation

Use three layers:

1. **Compile-time required capabilities** — build fails if absent.
2. **Boot-time discovered capabilities** — validated and narrowed from maxima.
3. **NVMe-advertised capabilities** — generated from the actual selected/validated implementation.

Example:

```text
FTL requires:
  media.async_read
  media.async_program
  media.async_erase
  media.oob_bytes >= metadata_layout.required_oob
  ecc.correctable_bits >= profile.minimum_ecc
  timers.monotonic_deadline

Optional:
  media.multi_plane
  media.cache_program
  transport.sgl
  controller.msix
```

An optional capability has an explicit `Unsupported` result or is compiled out. It never maps to a silent no-op.

---

## 8. Controller and media profile system

### 8.1 Profile source of truth

A profile should be declarative and reviewable. The following is illustrative Simple/SSpec-style pseudocode, not a claim that every syntax form exists today:

```simple
controller SimpleFpgaRv32:
    schema_version: 1
    cpu:
        isa: rv32imac
        endian: little
        harts: 1
        atomic_width: 32
    address:
        physical_bits: 32
        dma_bits: 32
    nvme:
        transport: pcie
        spec_ceiling: "2.4"
        queues:
            admin: 1
            io_max: 1
            depth_max: 16
        outstanding_max: 1
        prp: single_page
        sgl: false
    mmio:
        registers: import_systemrdl("rv32_nvme_axi.rdl")
    dma:
        coherent: false
        descriptors: 1
        max_transfer: 4096
        alignment: 4
    irq:
        mode: polling
    protection:
        pmp_regions: 8
        axi_firewall: true
    memory:
        firmware_region: 0x80000000..0x80100000
        mailbox_region:  0x80100000..0x80101000
        data_region:     0x80200000..0x80300000
```

A real board profile composes it with media:

```simple
board CosmosPlusReference:
    controller: CosmosPlusZynq7000
    media: ToshibaOnfiProfile
    wiring:
        channels: 8
        ways_per_channel: 8
    evidence_required: C5
```

### 8.2 Generated outputs

For each profile, generate:

- semantic constants and bounded types;
- MMIO register blocks with access mode (`ro`, `rw`, `w1c`, `doorbell`, `fifo`);
- register reset values and reserved-bit masks;
- controller and media capability traits;
- linker script fragments and memory sections;
- startup protection tables (PMP/MPU/firewall/IOMMU);
- DMA descriptor layouts and alignment assertions;
- RTL/VHDL/SystemVerilog packages and testbench constants;
- device-tree or Linux endpoint metadata where applicable;
- AOP facts and allowed access regions;
- conformance-test parameter sets;
- generated documentation and profile fingerprint.

### 8.3 Profile validation

Validation is not just schema syntax. The generator must prove equations such as:

```text
num_pages = channels × ways × luns × planes × blocks × pages_per_block
namespace_capacity_lbas ≤ usable_pages × sectors_per_page
metadata_bytes_per_page ≤ OOB budget after ECC/reserved markers
max_inflight_writes × per_write_buffers ≤ write-buffer pool
max_queues × queue_depth ≤ command-context capacity
DMA address bits ≥ all configured DMA windows
all MMIO registers fit their declared BAR/window
all PMP/firewall regions are representable and non-overlapping
hard_realtime_reserved_slots + background_max ≤ total_slots
journal checkpoint fits reserved metadata blocks
```

Overflow is checked in a wide compile-time integer domain. A profile with an overflowing or truncated equation is rejected.

### 8.4 Profile certification record

Each profile has a machine-readable record:

```text
profile_id
schema_version
source_hash
controller_revision
board_revision
media_part/revision scope
toolchain versions
supported command set/features
known errata and workarounds
certification level
last passing evidence bundle hashes
expiry/revalidation triggers
```

Changing a register offset, timing value, queue capacity, ECC layout, compiler version, or AOP policy invalidates affected evidence.

### 8.5 Controller contribution contract

A new controller profile is complete only when it provides:

1. profile schema and generated register definitions;
2. startup/reset/clock/cache implementation;
3. MMIO, DMA, IRQ, timer, watchdog, protection, and trace services;
4. queue/doorbell/PRP/SGL behavior supported by the profile;
5. simulator or RTL model where possible;
6. negative DMA/MMIO tests;
7. host enumeration/reset/admin/I/O tests;
8. evidence level and unsupported-feature list;
9. no controller-specific code inside FTL/reliability;
10. a legal/source-origin record.

---

## 9. Fully typed and highly adaptable firmware model

### 9.1 Type policy

Raw fixed-width integers are allowed at three boundaries only:

1. wire/register decoding;
2. generated hardware representation modules;
3. explicitly reviewed arithmetic kernels.

They are immediately converted to semantic types. Public service APIs use semantic types and `Result`, never sentinel integers such as `-1`, `UNMAP`, or `0` when absence/error has distinct meaning.

### 9.2 Required semantic type families

#### NVMe/host types

```text
ControllerId<P>
NamespaceId<P>
QueueId<Admin|Io, P>
QueueSlot<Q, P>
CommandId<Q>
CompletionPhase<Q>
Opcode<CommandSet>
Lba<Nsid>
LbaCount<Nsid>
SectorCount
ByteCount
DwordCount
HostVirtualAddress        # host model only
DmaAddress<Domain>
DmaLength
PrpEntry<Domain>
SglDescriptor<Kind, Domain>
StatusCodeType
StatusCode<Sct>
```

#### NAND/media types

```text
NandChannel<M>
NandTarget<M>
NandLun<M>
NandPlane<M>
NandBlock<M>
NandWordline<M>
NandPage<M>
Codeword<M>
Column<M>
Ppn<M>
PhysicalAddress<M>
EraseCount
ReadRetryLevel<M>
VrefOffset<M>
EccSyndrome<E>
CorrectedBitCount<E>
OobLayout<M, E>
```

#### Runtime/resource types

```text
PromiseId<Operation, Result, Error, Pool, Generation>
TaskId<TaskKind, Pool, Generation>
BufferId<BufferClass, Pool, Generation>
DescriptorId<Ring, Generation>
TimerId<Clock, Generation>
RingIndex<Ring>
PoolIndex<ObjectKind, Pool>
LeaseId<Resource, Owner, Generation>
CoreId<P>
PriorityClass
Deadline<Clock>
```

#### Hardware types

```text
MmioReg<Block, Offset, Width, AccessMode>
MmioValue<Reg>
IrqVector<Controller>
ClockTicks<Clock>
CacheLine<Controller>
PmpRegion<Owner>
DmaWindow<Domain>
```

### 9.3 Bounded types and checked construction

A constructor validates once:

```simple
fn queue_id<P, K>(raw: u16) -> Result<QueueId<K, P>, QueueIdError>
fn nand_block<M>(raw: u32) -> Result<NandBlock<M>, GeometryError>
fn dma_len<P>(raw: u32) -> Result<DmaLength<P>, DmaError>
```

Inside a verified module, operations preserve bounds. Indexing accepts only the corresponding bounded index type.

Avoid a design where every wrapper still contains unrestricted `i64` and every call can construct it directly. Constructors must be private or validated, and generated constants should create compile-time values.

### 9.4 Profile-bound coordinates

A page from media profile A must not index media profile B:

```text
NandPage<ToshibaProfile> != NandPage<MicronProfile>
Ppn<CosmosBoard>         != Ppn<HostReference>
```

For runtime-discovered media within a compiled family, include a boot-generation token:

```text
Ppn<MediaFamily, DiscoveryGeneration>
```

A handle from before media reset/re-discovery becomes invalid.

### 9.5 Typestate for initialization and reset

Model controller lifecycle as types/state machines:

```text
Controller<Cold>
  -> Controller<Clocked>
  -> Controller<MemoryProtected>
  -> Controller<TransportReady>
  -> Controller<AdminReady>
  -> Controller<IoReady>
  -> Controller<Quiescing>
  -> Controller<Resetting>
  -> Controller<Failed>
```

Methods are only available in legal states. For example, queue creation is unavailable before admin readiness, and DMA submission is unavailable while quiescing/resetting.

Media lifecycle:

```text
Media<Unidentified>
  -> Media<Identified>
  -> Media<TimingConfigured>
  -> Media<MetadataRecovered>
  -> Media<Online>
  -> Media<Degraded|ReadOnly|Failed>
```

### 9.6 Wire decode and validation

Do not pass a raw 64-byte command into the FTL. Decode in phases:

1. copy/validate command memory under DMA rules;
2. parse common header;
3. dispatch known opcode/command set;
4. validate reserved bits, namespace, range, transfer size, PRP/SGL, fused operation, metadata/protection information;
5. construct a typed command;
6. admit resources;
7. execute.

Example:

```text
RawSqe
  -> ParsedSqe
  -> ValidatedWrite<Nsid, TransferShape, ProtectionMode>
  -> AdmittedWrite<CommandContext, DataLease, JournalCredit>
```

A malformed command cannot reach FTL state mutation.

### 9.7 Arithmetic policy

- Use explicit checked add/multiply/shift for address and capacity calculations.
- Use saturating arithmetic only for telemetry counters where saturation is specified and observable.
- Never saturate a physical address, queue slot, journal sequence, or mapping index.
- Require explicit unit conversion (`lbas.to_bytes(format)`, not `lbas * 4096`).
- Prove alignment through types, not repeated masks.
- Distinguish wrapping hardware counters from monotonic software epochs.

### 9.8 Configuration adaptability without hot-path cost

Adaptability comes from generated profiles and static specialization, not dynamic maps in the hot path.

- Compile-time constants define maxima and memory layout.
- Boot discovery narrows actual geometry/capabilities.
- Optional features are statically included and represented by sealed capability traits.
- Profile-specific fast paths are behind typed interfaces and monomorphized.
- Host/reference builds may use dynamic adapters; device builds do not.

---

## 10. Full embedded Promise/async design

### 10.1 Separate runtime from the general Promise

Do not modify the general host Promise until it somehow becomes safe by convention. Define a distinct embedded implementation:

```text
std.embedded.async
std.embedded.async.hrt
std.embedded.async.pool
```

It may expose familiar `async`/`await` syntax, but compilation lowers each function to a fixed state machine with statically known retained fields.

The design can learn from embedded executors such as Embassy—no heap, statically allocated task state, precise wakeups—but Simple firmware requires additional SSD-specific guarantees:

- fixed operation pools and hard admission limits;
- typed promise IDs instead of general references;
- explicit resource leases retained across awaits;
- bounded continuation topology;
- deadline and cancellation state;
- per-core ownership and MDSOC+ transfer rules;
- formal ring and completion invariants;
- release evidence for maximum memory and execution cost.

### 10.2 Promise representation

Illustrative representation:

```simple
struct EmbeddedPromiseSlot<Op, R, E>:
    generation: Generation
    state: PromiseState<Op>
    owner: OwnerId
    priority: PriorityClass
    deadline: Option<Deadline>
    cancel: CancelState
    wait_resource: WaitResource
    resume_pc: ResumePoint<Op>
    result: MaybeUninit<Result<R, E>>
    retained: RetainedState<Op>
```

The slot lives in a typed fixed arena:

```text
PromisePool<NandReadOp, 64>
PromisePool<NandProgramOp, 32>
PromisePool<DmaOp, 64>
PromisePool<NvmeCommandOp, 128>
```

Pools may be generated from the profile. They are not one untyped global pool.

### 10.3 Promise state machine

A common lifecycle is:

```text
Free
  -> Reserved
  -> Admitted
  -> Submitted
  -> WaitingResource | WaitingDma | WaitingNand | WaitingIrq | WaitingTimer
  -> Completing
  -> Resolved | Rejected | TimedOut | Cancelled
  -> Reclaimable
  -> Free(next generation)
```

Illegal transitions trap in debug/test and produce a fail-closed controller error/reset path in production according to profile policy.

Key rules:

- `Reserved` owns no durable mutation yet.
- `Admitted` means all required credits/resources are held.
- A promise can have one current wait reason.
- Completion is idempotent by operation epoch and generation.
- A late IRQ/DMA/NAND completion for a reclaimed generation is rejected and counted.
- `Cancelled` does not imply the hardware operation stopped; cancellation policy tracks whether the operation is abortable, drain-only, or must complete and discard.
- Reclamation occurs only after all hardware and child-operation references are released.

### 10.4 Await lowering

An embedded async function:

```simple
async fn write(cmd: ValidatedWrite) -> Result<Completion, IoError>:
    val admitted = await admit_write(cmd)
    val data = await dma_in(admitted.host_range)
    val txn = await ftl_prepare(admitted.lba, data)
    await nand_program(txn.target, data, txn.oob)
    await journal_commit(txn)
    complete_write(cmd.cid)
```

lowers conceptually to:

```text
state 0: validate retained inputs; request admission; wait AdmissionEvent
state 1: store AdmissionLease; submit DMA; wait DmaCompletion
state 2: store BufferLease; prepare FTL transaction; wait allocation/journal credit
state 3: submit NAND; wait NandCompletion
state 4: submit journal commit; wait durable completion
state 5: post NVMe completion; release leases; resolve
```

No closure object or callback list is created. Retained variables become explicit fields whose total size is reported at build time.

### 10.5 Bounded combinators

Provide only statically bounded device combinators:

- `join2`, `join3`, `join_const<N>` where `N` is profile-bounded;
- `race2` with explicit losing-operation cancellation/drain policy;
- `timeout` using one timer slot;
- `retry_const<N>` with typed retry policy;
- `select_ring<RingSet>` where ring set is compile-time fixed.

Do not provide device-side `Promise.all(dynamic_list)` or arbitrary callback registration.

### 10.6 Scheduler lanes

Recommended lanes:

| Lane | Examples | Scheduling |
|---|---|---|
| Interrupt/ack | PCIe, DMA, NAND ready/busy, timer | Highest priority; acknowledge, snapshot status, enqueue event, return. |
| Hard real-time transport | SQ fetch, CQ posting, timeout, reset | Reserved slots and credits; bounded work per wake. |
| Foreground media | reads/writes/flush | Weighted/fair queues with deadlines and channel awareness. |
| Recovery | journal replay, metadata repair, degraded read | Explicit admission and watchdog; can preempt background work. |
| Background | GC, wear leveling, refresh, scrub, telemetry aggregation | Credit-limited; yields on foreground pressure. |

No task can run an unbounded loop per wake. Each poll has a generated or reviewed work budget.

### 10.7 Rings and wakeups

Use single-producer/single-consumer rings where topology permits. Use bounded MPSC only where required, with clear atomic and cache-coherency rules.

Each ring defines:

```text
producer owner(s)
consumer owner
entry type
capacity
full policy
empty policy
memory ordering
cache maintenance
sequence/epoch behavior
maximum residence time
telemetry counters
```

The ring entry contains IDs and immutable small values, not raw pointers to mutable objects.

Example:

```text
NandCompletionEvent {
    op: PromiseId<NandOp, ...>,
    generation: Generation,
    status: NandStatus,
    corrected: CorrectedBitCount,
    hardware_epoch: MediaEpoch
}
```

### 10.8 Resource admission

A write must reserve all resources that could otherwise deadlock midway:

- command context;
- data-buffer/DMA descriptor credit;
- mapping transaction context;
- media-operation slot;
- journal record/metadata credit;
- completion queue credit or a guaranteed completion-reserve mechanism.

When full admission is too expensive, define a proven partial-order of acquisition and release. CI/formal checks verify that no wait cycle exists.

### 10.9 Cancellation, timeout, reset

Each operation type declares:

```text
abortable_before_submit
abortable_after_submit
completion_may_arrive_after_cancel
resources_retained_until_drain
reset_invalidates_epoch
idempotent_retry conditions
```

Controller reset increments transport epoch. Media reset increments media epoch. Promise IDs include or reference the relevant epoch so stale completions cannot mutate new state.

### 10.10 Memory and timing receipts

The compiler emits:

- count and byte size of every task/promise slot;
- retained fields per async function;
- maximum ring memory;
- maximum timer slots;
- maximum nested bounded combinators;
- stack bound for non-async calls;
- maximum operations per poll where statically derivable;
- unresolved dynamic timing obligations requiring measurement.

A mission-critical build fails if a new async path lacks a bounded memory receipt or introduces an unapproved unbounded loop/recursion.

---

## 11. Index-based pointers and allocator design

### 11.1 Goals

The allocator must provide pointer-like ergonomics without exposing addresses or backing arrays. It must be usable on bare metal, deterministic, and suitable for formal reasoning.

Core type:

```text
Index<T, Pool, Generation, Rights>
```

where `Rights` can be `Owned`, `MutBorrow`, `SharedRead`, `Transfer`, or a resource-specific lease.

### 11.2 Opaque arena

Illustrative API:

```simple
opaque struct Arena<T, P, const N: usize>
opaque struct Index<T, P, G, R>

fn reserve(arena: &mut Arena<T, P, N>) -> Result<ReservedIndex<T, P>, PoolFull>
fn initialize(slot: ReservedIndex<T, P>, value: T) -> OwnedIndex<T, P>
fn read(arena: &Arena<T, P, N>, id: SharedIndex<T, P>) -> Result<&T, HandleError>
fn mutate(arena: &mut Arena<T, P, N>, id: MutIndex<T, P>) -> Result<&mut T, HandleError>
fn transfer(id: OwnedIndex<T, P>, owner: OwnerId) -> TransferToken<T, P>
fn accept(token: TransferToken<T, P>, owner: OwnerId) -> OwnedIndex<T, P>
fn release(arena: &mut Arena<T, P, N>, id: OwnedIndex<T, P>) -> Result<(), HandleError>
```

Only the arena module can index storage. Callers cannot access `slots`, `used`, `generation`, or free-list fields.

### 11.3 Pool classes

Do not combine all resources into one arena:

- NVMe command contexts;
- admin and I/O queue objects;
- DMA descriptors;
- small metadata buffers;
- full-page data buffers;
- NAND operation contexts;
- FTL mapping transactions;
- GC/refresh/recovery tasks;
- journal records;
- telemetry events.

Separate pools improve typing, isolation, admission analysis, cache layout, and fault containment.

### 11.4 Generation and ABA policy

Generation indices prevent a stale handle from silently referencing a replacement object. Generation wrap must also be addressed.

Policy:

1. Use a profile-selected generation width with a calculated lifetime bound.
2. Before wrap, permanently retire the slot rather than reuse a key.
3. Maintain `retired_slots` telemetry.
4. Reserve enough non-retired slots for hard-real-time minimum capacity.
5. Fail boot/profile certification if worst-case operation rate could exhaust safe generations within required service life.
6. Increment a pool epoch on destructive reset/reinitialization.
7. Include controller/media epoch in hardware-facing operations to reject late completions.

A pool with a saturated generation cannot silently keep returning the old generation.

### 11.5 Allocation algorithm

Default embedded arena:

- fixed-size array placed in a named linker section;
- fixed-size bitmap or intrusive index free list;
- O(1) or bounded O(word count) reserve/release;
- no coalescing;
- no unbounded scan in hard-real-time pools;
- per-core local pools or SPSC transfer queues to avoid global locks;
- optional background compaction only for host/reference structures, never index identity.

### 11.6 Ownership and MDSOC+ transfer

A mutable resource has one owner. Sending an owned handle through a ring transfers ownership permanently unless an explicit return token is part of the protocol.

```text
Core A: Owned<Buffer>
  --send TransferToken--> Core B
Core A: no rights
Core B: Owned<Buffer>
```

Shared immutable views require a bounded reference/lease protocol or static lifetime. Avoid general atomic reference counting in hard-real-time paths.

### 11.7 DMA buffers

A DMA buffer handle contains no directly usable physical address outside the DMA service:

```text
BufferId<Page4K, DataPool, Gen>
DmaLease<BufferId, Direction, Domain, Epoch>
```

The DMA service validates:

- ownership;
- length and offset;
- alignment;
- direction;
- controller DMA window;
- cache state;
- IOMMU mapping;
- descriptor capacity;
- host-range validation;
- completion epoch.

Only the service can reveal the address to generated BSP code.

### 11.8 Poisoning, zeroization, and quarantine

On release:

- mark slot non-live before making it free;
- increment/retire generation;
- clear ownership and sensitive metadata;
- zero or poison based on pool class;
- quarantine after detected corruption or double release;
- preserve a bounded forensic record without retaining live pointers.

### 11.9 Allocator verification

Required properties:

- unique live `(pool,index,generation)`;
- stale handle rejected;
- double release rejected;
- owner mismatch rejected;
- no read before initialization;
- no mutation through shared rights;
- transfer removes sender rights;
- no slot appears simultaneously in free and live sets;
- live + free + retired + quarantined = capacity;
- hard-real-time reserve cannot be consumed by background class;
- generation wrap cannot create a previously valid key.

Property tests, model checking, and negative compile tests should cover these independently.

---

## 12. Real NAND and emulator architecture

### 12.1 One opaque media service

FTL and reliability code use only a typed async `MediaService`/`NandPort`. They do not own the backend object.

Illustrative interface:

```simple
trait NandPort<M: MediaProfile>:
    async fn discover(target: NandTarget<M>) -> Result<DiscoveredMedia<M>, DiscoverError>
    async fn reset(target: NandTarget<M>) -> Result<(), NandError>
    async fn configure_timing(cfg: TimingSelection<M>) -> Result<(), NandError>
    async fn read(req: NandReadReq<M>, dst: BufferLease) -> Result<NandReadResult<M>, NandError>
    async fn program(req: NandProgramReq<M>, src: BufferLease) -> Result<NandProgramResult, NandError>
    async fn erase(req: NandEraseReq<M>) -> Result<NandEraseResult, NandError>
    async fn get_feature(req: FeatureRead<M>) -> Result<FeatureValue<M>, NandError>
    async fn set_feature(req: FeatureWrite<M>) -> Result<(), NandError>
    async fn read_retry(req: ReadRetryReq<M>, dst: BufferLease) -> Result<NandReadResult<M>, NandError>
    fn health_snapshot() -> MediaHealthSnapshot<M>
```

Fault injection is intentionally absent.

### 12.2 Real NAND backend

The real backend owns:

- FMC/NAND controller registers;
- channel/way arbitration;
- NAND command sequencing;
- ready/busy and timeout handling;
- controller DMA and data buffers;
- ECC engine configuration and syndrome/result collection;
- timing/training state;
- retry/read-reference controls;
- reset and error recovery;
- bad-block marker reads;
- media status translation.

It exposes semantic results, not register values.

### 12.3 Discovery and boot

Boot flow:

1. reset controller and channels;
2. establish conservative timing;
3. enumerate targets/LUNs;
4. read multiple parameter-page copies and validate signatures/CRC;
5. reconcile generated family limits with discovered geometry;
6. load vendor quirk/read-retry module by validated ID/profile;
7. configure timing and train/verify;
8. sample factory-bad markers without modifying media;
9. recover persistent metadata/journal;
10. run non-destructive media sanity tests;
11. enter online/read-only/degraded/failed state.

Unknown media must not fall through to an approximate compatible profile. It can enter a diagnostic/read-only mode or fail boot.

### 12.4 Page, OOB, and ECC fidelity

A production media model and real backend operate on full byte spans/codewords:

```text
PageData<M>
OobData<M>
CodewordSpan<M,E>
MetadataLayout<M,E>
```

The existing one-`i64` payload remains a teaching/fast-algorithm model named accordingly, for example `ScalarPageTeachingModel`. It cannot implement the production `FullPageMediaEvidence` marker.

ECC policy includes:

- codeword boundaries;
- protected main/OOB bytes;
- parity placement;
- erased-page detection;
- corrected-bit reporting;
- uncorrectable classification;
- miscorrection defenses where applicable;
- retry interaction;
- scrub/refresh thresholds;
- controller-vs-software ECC capability.

### 12.5 Persistent metadata and power loss

A real firmware profile needs an explicit durability contract:

- what constitutes a completed NVMe write;
- volatile write-cache policy and Flush semantics;
- journal/checkpoint format and version;
- atomic update unit;
- sequence/epoch rules;
- torn-page/torn-program detection;
- metadata redundancy and checksum/ECC;
- replay idempotence;
- orphan/new-page handling;
- bad block during metadata update;
- emergency shutdown/power-loss signal behavior;
- boot-time bounded recovery.

No emulator-only in-memory map may substitute for persistent recovery evidence.

### 12.6 Emulator/test-model isolation

Test models live in a dependency subtree forbidden to production builds.

Recommended tiers:

| Tier | Purpose | Fidelity |
|---|---|---|
| T0 scalar/algorithm | Very fast FTL/unit tests | Small integer payload; explicitly non-media-faithful. |
| T1 functional full-page | NAND program/read/erase, OOB, bad blocks, ECC codeword layout | Full bytes and geometry, deterministic. |
| T2 timing/controller | Channels, LUN busy time, DMA, queue contention, interrupts | Event/timing model. |
| T3 reliability/fault | Retention, disturb, wear, read-retry, program/erase/read failures | Parameterized stochastic/deterministic faults with seeded replay. |
| T4 RTL/pin/co-sim | FMC/PHY bus protocol and firmware-in-loop | RTL or protocol transactor. |
| T5 real media HIL | Actual NAND and controller | Hardware evidence. |

A test result always states the tier.

### 12.7 Test-control port replacing direct `.nandram`

The test harness controls faults through a separate, typed capability that is not visible to production firmware.

```simple
trait MediaTestControl<M>:
    fn inject_program_failure(target: NandBlock<M>, occurrence: Occurrence) -> FaultId
    fn inject_erase_failure(target: NandBlock<M>, occurrence: Occurrence) -> FaultId
    fn inject_read_errors(target: NandPage<M>, pattern: ErrorPattern) -> FaultId
    fn advance_time(delta: SimulatedDuration)
    fn set_wear(target: NandBlock<M>, cycles: EraseCount)
    fn power_cut(at: FaultTrigger)
    fn snapshot(query: SnapshotQuery<M>) -> ImmutableSnapshot
```

Properties:

- the harness receives the capability; normal firmware does not;
- requests are validated and logged;
- snapshots are copies/immutable summaries, never references to backing arrays;
- each fault has an ID, trigger, scope, seed, and outcome;
- model state remains private;
- the control channel is separate from the NVMe data path;
- the production linker graph has no `MediaTestControl` implementation.

For RTL simulation, this can be a dedicated testbench control interface or protected VHDL procedure. For QEMU, use a QMP/test device or shared test-control protocol—not GDB raw writes into firmware storage.

For hardware engineering images, fault control requires a debug strap/fuse, signed engineering image, authenticated session, and audit log. Production images omit the code.

### 12.8 Observability

Production observability returns safe telemetry:

- operation counts and latency histograms;
- corrected-bit distributions;
- retry-depth histograms;
- bad-block/retired-block counts;
- wear buckets;
- queue depth and backpressure;
- recovery reasons;
- controller errors and resets.

It does not return mutable storage or arbitrary physical reads. A forensic raw-media command, if ever needed, is a separately authorized service with explicit security and data-integrity policy—not a normal struct field.

---

## 13. AOP verification of direct and illegal access

### 13.1 Role of AOP

AOP defines and enforces architecture policy across source, generated code, compiler IR, link artifacts, and runtime protection setup. It may also weave low-overhead tracing or checks at approved boundaries, but it does not replace the interfaces.

The access proof has five layers:

1. dependency/import/call policy;
2. typed HIR/MIR effect and provenance verification;
3. link/relocation/section verification;
4. post-link machine-code/address verification;
5. runtime memory/bus/DMA protection.

No single layer is accepted as complete alone.

### 13.2 Source/dependency policy

Simple-like illustrative policy:

```simple
# Production cannot depend on any test model or control API.
forbid pc{ import(test_models.**) within(src.firmware.nvme_ssd.prod.**) }
forbid pc{ depend(within(src.firmware.nvme_ssd.prod.**), within(test_models.**)) }
forbid pc{ depend(within(ftl.**), within(bsp.**)) }
forbid pc{ depend(within(ftl.**), within(services.controller.impl.**)) }

# Only the media service implementation can call backend NAND operations.
allow  pc{ call(backends.nand.**::*) within(services.media.impl.**) }
forbid pc{ call(backends.nand.**::*) within(!services.media.impl.**) }

# Only the controller/DMA services can use hardware access primitives.
allow  pc{ call(hw.mmio.**::*) within(services.controller.impl.**) }
forbid pc{ call(hw.mmio.**::*) within(!services.controller.impl.**) }
allow  pc{ call(hw.dma.**::*) within(services.dma.impl.**) }
forbid pc{ call(hw.dma.**::*) within(!services.dma.impl.**) }
```

These rules apply after macro expansion and generic instantiation, not only to lexical imports.

### 13.3 Required new IR pointcuts

Add pointcuts/facts such as:

```text
mem_read(region, type, provenance)
mem_write(region, type, provenance)
mmio_read(register, width)
mmio_write(register, width, value_mask)
dma_map(domain, range, direction)
dma_descriptor_write(engine, field)
raw_address_construct(source)
raw_pointer_cast(from, to)
inline_asm(effect_set)
ffi_call(symbol, declared_effect_set)
section_reference(section)
relocation_reference(symbol_or_region)
capability_acquire(resource)
capability_transfer(resource, from, to)
arena_access(pool, index_kind, operation)
```

Policy examples:

```simple
forbid pc{ mem_access(region("nandemu.*")) within(!test_models.media.**) }
forbid pc{ mem_access(region("arena.*.backing")) within(!runtime.alloc.impl.**) }
forbid pc{ mmio_access(*) within(!services.controller.impl.**) }
forbid pc{ dma_descriptor_write(*) within(!services.dma.impl.**) }
forbid pc{ raw_address_construct(*) within(prod.**) }
forbid pc{ raw_pointer_cast(*) within(prod.**) }
forbid pc{ inline_asm(effect = unknown) within(prod.**) }
forbid pc{ ffi_call(effect = unknown) within(prod.**) }
```

The exact syntax can differ, but the semantic coverage is mandatory.

### 13.4 Effect declarations and inference

Hardware boundary functions declare effects:

```simple
@effects(mmio_read(NvmeRegs.CSTS), mmio_write(NvmeRegs.CC))
unsafe fn controller_enable(...)
```

The compiler infers transitive effects and verifies declarations are complete. An FFI or assembly block with an incomplete effect declaration fails a mission-critical build.

Effects are parameterized where possible:

```text
nand_read(target page)
dma_read(host range -> buffer lease)
mmio_write(generated register)
allocator_mutate(typed pool)
```

### 13.5 Region provenance

Every addressable object receives a region/provenance class:

- firmware code/read-only data;
- per-core stack;
- typed arena backing store;
- DMA buffers;
- queue memory;
- MMIO register window;
- real NAND controller aperture;
- test model private state;
- host-shared mailbox;
- journal/recovery scratch.

Loads/stores preserve provenance through pointer arithmetic and casts. Losing provenance is illegal outside an unsafe boundary.

### 13.6 Generated access manifest

The compiler emits a manifest such as:

```text
component media_service:
  can_call: [nand_backend]
  memory:
    read_write: [media_context_pool, nand_dma_buffers]
    read_only: [media_profile]
  mmio:
    read_write: [FMC0, FMC1]
  dma:
    domains: [nand_dma]
  forbidden: [host_prp_raw, nandemu_private]

component ftl:
  can_call: [media_service, journal_service, allocator_service]
  memory:
    read_write: [ftl_context_pool]
  mmio: []
  dma: []
```

The profile generator, compiler, linker verifier, and platform startup all consume the same manifest.

### 13.7 Link and binary verification

Production verification checks:

- no test/emulator object files in link inputs;
- no symbols with forbidden ownership tags;
- no `.nandemu`, `.fault_model`, `.mock`, `.test_control`, or unapproved debug sections;
- no relocations to forbidden symbols/regions;
- no exported test hooks;
- no raw `.nandram` symbol contract exposed to host scripts;
- linker map matches generated memory layout;
- disassembly contains no unclassified absolute MMIO/private-region constants;
- indirect-call target sets are closed and approved;
- LTO/inlining did not erase effect provenance from the receipt;
- firmware hash binds the access receipt and policy hash.

Machine-code scans are a defense-in-depth check because constants can collide. Typed IR provenance and relocations are the primary static proof.

### 13.8 Runtime protection

Where hardware permits:

- put media-model/test state in an inaccessible region during co-sim;
- configure PMP/Smepmp so only service code/data domains can access designated regions;
- use U/S/M separation or process separation where available;
- restrict DMA engines to explicit IOMMU/AXI windows;
- use AXI protocol/firewall assertions to reject unapproved masters/ranges;
- lock protection configuration after boot;
- record precise traps with component, address, operation, PC, and profile hash;
- reset/quarantine on violation according to safety mode.

On a minimal single-mode core lacking PMP, static proof and bus/firewall logic become release requirements rather than optional hardening.

### 13.9 Negative access corpus

Every rule has at least one test that deliberately tries to bypass it:

1. `ftl` indexes `nand.page_data` directly.
2. test code writes `_nandram_start + offset`.
3. a helper function hides the direct access.
4. a generic function instantiates with emulator storage.
5. a macro expands to an MMIO literal write.
6. FFI returns a raw pointer to media state.
7. inline assembly loads a forbidden address.
8. code mutates a DMA descriptor field outside DMA service.
9. code forges a pool index/generation.
10. code accesses arena backing arrays.
11. production code imports a fault injection method.
12. a symbol is referenced only through a function pointer.
13. a test-only object is pulled in by an apparently unused generic.
14. a raw address is split/constructed arithmetically to evade constant scan.
15. a stale completion uses a new promise generation.

A negative test passes only when rejected/trapped for the intended reason. A parser error or unrelated build failure is not a pass.

### 13.10 AOP acceptance criteria

- zero unclassified external effects;
- zero unclassified loads/stores into protected regions;
- zero production dependencies on test/emulator modules;
- all negative tests rejected or trapped;
- generated manifest equals compiler-observed effect graph;
- runtime protection setup matches manifest;
- proof/access receipt hash is included in the evidence bundle;
- no measurable hot-path overhead from compile-time-only checks;
- optional runtime guards have separately measured overhead and explicit profile policy.

---

## 14. Fake, mock, stub, and shortcut hardening

### 14.1 Terminology

Use precise labels:

| Label | Meaning | Production allowed? |
|---|---|---|
| Reference model | Independently specified semantic model used as oracle | Not linked into firmware; allowed in tests. |
| Emulator | Models a hardware/media interface and state | Test image only. |
| Simulator | Models timing/system behavior | Test/analysis only. |
| Mock | Verifies expected interactions, often programmed by a test | Test only. |
| Fake | Simplified working implementation, e.g. in-memory media | Test/example only unless explicitly certified as the actual product backend. |
| Stub | Returns canned or minimal responses | Test only. |
| Fault injector | Alters modeled or hardware behavior through controlled interface | Test/engineering image only. |
| Shortcut | Skips required behavior while presenting success or full capability | Forbidden. |
| Placeholder | Incomplete code marked for future implementation | Forbidden in production dependency closure. |

A one-word page model is a **teaching fake**, not "real NAND." A DRAM-backed NVMe endpoint is a real endpoint but a **non-NAND backend**. A no-op Vref setter on a backend without Vref is not an implementation; it must be absent or return `Unsupported`.

### 14.2 Automated shortcut detector

Add a semantic lint and binary check for:

- names/comments containing `fake`, `mock`, `stub`, `dummy`, `placeholder`, `TODO`, `FIXME`, `unimplemented`, `temporary`, `hack`, `no-op`;
- constant success/error results;
- empty methods;
- zero-filled or repeated-pattern reads;
- memory copy standing in for DMA/NAND without an explicit model type;
- one-byte/one-word payload standing in for full pages;
- hard-coded Identify, SMART/health, namespace, or capacity data disconnected from profiles;
- hard-coded queue addresses/counts/depths outside generated code;
- modulo aliasing of large geometry into small arrays;
- test hooks on production-facing structs;
- disabled verification under release flags;
- "best effort" fallback after an unsupported hardware operation;
- marker-only tests whose implementation prints the marker unconditionally;
- the same function used both as implementation and expected-value oracle;
- a proof file not tied to the compiled artifact hash;
- production link inclusion of test/emulator libraries.

The lint generates findings, not blind failures for every word. Each finding must be classified in a checked manifest. Unclassified findings fail production CI.

### 14.3 Capability truthfulness

Every feature follows one of four states:

```text
NotCompiled
CompiledUnsupportedOnProfile
SupportedUncertified
SupportedCertified(level, evidence)
```

NVMe Identify/log pages advertise only `SupportedCertified` features at the required release level. Development images may expose uncertified features with a distinct identity and warning log, never as production firmware.

### 14.4 Test-double isolation

- Test doubles are in `test_models/` or `tests/fixtures/` only.
- Production modules cannot import their interfaces.
- Test adapters implement production interfaces from the test side.
- Test-control capabilities are constructed by the harness, not by firmware code.
- Build tags alone are insufficient; dependency and link verification must prove absence.
- Test binary signing keys and production signing keys are separate.

### 14.5 Independent oracle rule

For each critical property, use an independent oracle or invariant:

| Property | Independent evidence |
|---|---|
| NVMe command status/fields | NVM Express spec vectors + pynvme/nvme-cli/Linux host behavior. |
| Queue/doorbell state | RTL assertions and host-observed completions. |
| Mapping correctness | Separate compact reference model + property tests. |
| Recovery | Crash-state enumerator and persistent image replay, not only firmware self-check. |
| NAND protocol | Bus/protocol monitor or controller model independent of firmware driver. |
| ECC | Known vectors and independent encoder/decoder implementation. |
| Allocator | Formal/model checker + corruption/mutation tests. |
| AOP access | Compiler receipt + linker verifier + runtime firewall negative test. |

### 14.6 Mutation testing

Seed mutations that a robust suite must catch:

- skip journal flush before completion;
- post CQ entry before data DMA finishes;
- swap LBA and PPN types through an unsafe cast;
- omit queue phase toggle;
- reuse stale generation;
- ignore NAND timeout;
- convert ECC failure to success;
- fail to clear old mapping after remap;
- allow background pool to consume reserved foreground credit;
- make Vref/read-retry a no-op while reporting success;
- bypass media service and write model memory;
- remove reset epoch check;
- drop cache maintenance on noncoherent DMA;
- advertise unsupported SGL or Flush behavior.

Release tests should demonstrate a high kill rate for the critical mutation set.

---

## 15. Verification and automation architecture

### 15.1 Test pyramid and evidence matrix

| Layer | Runs on each PR | Nightly | Release | Evidence grade |
|---|---:|---:|---:|---|
| Formatting, generated diff, doc/link checks | Yes | Yes | Yes | D |
| Compiler/AOP negative tests | Yes | Yes | Yes | D |
| Unit/property/model tests | Yes | Yes | Yes | C/D |
| Host sanitizers/static analysis | Yes where fast | Yes | Yes | C/D |
| Profile compile matrix | Selected profiles | All profiles | All certified profiles | D |
| QEMU bare-metal boot | Yes | Yes | Yes | C |
| GHDL/Verilator firmware-in-loop | Selected smoke | Full matrix | Full certified matrix | B |
| FEMU/NVMeVirt differential | Selected | Full | Full | C |
| pynvme/nvme-cli/blktests/SPDK/fio | Emulator subset | Lab hardware | Destructive certified HIL | A/B/C by target |
| FPGA synthesis/timing | Fast/open smoke | Vendor full | Locked tool/version full | B |
| PCIe endpoint HIL | No/shared lab subset | Scheduled | Mandatory | B/A transport |
| Real NAND HIL | No | Scheduled | Mandatory for C5+ | A |
| Power-cut/endurance/fault campaigns | No | Sample | Mandatory campaign | A |
| Formal/model checking | Changed proof scope | Full | Full | D plus proof artifact |
| Reproducible build/SBOM/signing | Sample | Yes | Mandatory | Release evidence |

### 15.2 Fast PR pipeline

Recommended sequence:

1. profile/schema syntax and semantic validation;
2. regenerate all affected outputs and require clean diff;
3. compile dependency graph and AOP source policy;
4. compile negative-access corpus and check expected diagnostics;
5. build changed profiles in host/reference mode;
6. run unit/property tests for changed modules;
7. run shortcut/fake/mock semantic lint;
8. run host sanitizers and undefined-behavior checks where applicable;
9. build `SimpleFpgaRv32` direct image;
10. QEMU boot smoke;
11. GHDL firmware-in-loop smoke using typed test-control, not `.nandram` offsets;
12. emit evidence bundle and compare size/memory/timing budgets.

Failing focused tests run first. After the first failing class is fixed, run the complete affected suite, then the global release subset. Do not repeatedly start the entire slow suite before local failures are resolved.

### 15.3 Profile compile matrix

Dimensions:

```text
controller profile
media profile
CPU ISA/width
endianness
single/multicore
polling/interrupt mode
coherent/noncoherent DMA
queue count/depth
command-set selection
safety mode
optimization/LTO mode
emulator fidelity tier (test only)
```

Use pairwise/covering arrays on PRs and full supported combinations nightly/release. Illegal controller/media pairs are compile-fail tests.

### 15.4 Host differential suite

Run the same command/fault traces against:

- Simple `HostReference`;
- Simple firmware plus controller model;
- FEMU where semantics overlap;
- NVMeVirt where semantics overlap;
- real controller profile in HIL.

Normalize implementation-specific timing but compare:

- command completion/status;
- Identify/log field truthfulness;
- data/checksum;
- reset and queue lifecycle;
- namespace bounds;
- malformed PRP/SGL behavior;
- power/fault outcome classes;
- durability after declared completion/flush;
- telemetry invariants.

Differential disagreement is triaged against the specification; external emulators are not automatically authoritative.

### 15.5 Host conformance and workload tools

Use:

- **pynvme** for arbitrary commands, BAR/config access, interrupts, checksums, multi-controller tests, fuzz/property generation;
- **nvme-cli/libnvme** for standardized admin/I/O operations and logs;
- **Linux blktests** for block/NVMe reset, fabrics/driver, and regression cases where applicable;
- **SPDK perf/examples** for user-space high-throughput queue behavior;
- **fio** for workload, data verification, latency, trim/flush, reset/recovery sequences;
- kernel filesystems only after raw block correctness gates pass.

Destructive suites require a lab inventory system that proves the selected namespace/device is disposable.

### 15.6 RTL/co-simulation

Required assertions/monitors include:

- legal AXI/PCIe handshake and no response loss;
- doorbell and queue pointer monotonic/phase rules;
- no DMA outside configured windows;
- no completion before required data/durability point;
- reset drains/invalidates all epochs;
- interrupt cause/vector correctness;
- no duplicate completion for `(qid,cid,epoch)`;
- no stale completion mutating new queue state;
- bounded liveness under fair hardware response;
- media-controller protocol sequences and timeout handling;
- test-control cannot alter production-visible memory except through declared fault semantics.

Replace the current raw word-offset injection with a control transaction such as:

```text
TB -> TestControl: InjectRetentionFault(page=X, trigger=next_read)
TB <- TestControl: FaultId=17
Host -> NVMe: read LBA...
TB <- EventLog: FaultId=17 triggered at media op 42
TB <- Snapshot: recovery_count=1, remap=(old,new), invariant_hash=...
```

### 15.7 Real NAND HIL

Minimum C5 campaign:

1. identify every target and validate parameter pages;
2. safe timing-mode selection/training across temperature/voltage test range available to lab;
3. full-page/OOB read/program/erase with independent data verification;
4. factory-bad scan and no accidental erase/program of factory-bad blocks;
5. ECC vectors and controlled error injection where hardware permits;
6. read-retry behavior and recovery thresholds;
7. program-order/partial-program restrictions;
8. multi-channel/way concurrency and timeout isolation;
9. bad block during data and metadata operations;
10. controller reset during each operation phase;
11. power cut during journal, data program, mapping update, GC, and checkpoint;
12. repeated boot/recovery with bounded time;
13. wear/retention/disturb campaigns or validated accelerated models plus sample hardware correlation;
14. no raw debug/test access in the production image.

### 15.8 Fuzzing

Fuzz inputs:

- all command dwords and reserved fields;
- queue sizes, alignment, head/tail wrap and phase;
- PRP lists, SGL chains, length/overflow, cycles, invalid mappings;
- namespace/LBA/count boundaries;
- interrupt ordering and coalescing;
- reset/link-down/timeouts at every state;
- NAND completion status and latency sequences;
- fault-control traces for test models;
- journal/checkpoint bytes and torn writes;
- controller/media parameter pages;
- profile files and generated register schemas.

The fuzzer records deterministic seeds and produces a minimized typed trace.

### 15.9 Formal/model-check targets

Prioritize small, high-value state machines:

- generational arena uniqueness/no stale dereference;
- ring full/empty/sequence invariants;
- promise legal transitions and exactly-once resolution;
- resource admission deadlock freedom;
- queue completion uniqueness and phase behavior;
- reset epoch invalidation;
- mapping transaction atomicity;
- journal replay idempotence;
- no acknowledged write is lost under the selected durability contract;
- bad-block retirement preserves mapping validity;
- AOP capability graph cannot reach forbidden resources;
- profile capacity equations and no integer overflow.

Use executable models/property tests for broad exploration and Lean/model checking for critical invariants. Proofs must bind to generated constants and implementation hashes.

### 15.10 Evidence bundle

Every significant run emits:

```text
evidence/
  manifest.json
  source_revision.txt
  dirty_tree.patch-or-empty
  compiler_hash.txt
  tool_versions.json
  profile_source + profile_hash
  generated_hashes.json
  aop_policy + access_receipt
  linker_map + section/symbol report
  firmware_image + image_hash
  test_vector/seed
  host/controller/media inventory
  simulator/RTL/HIL logs
  assertions/results.json
  coverage/mutation report
  performance/memory budgets
  signatures/attestations
```

A release claim points to an immutable bundle, not an informal console transcript.

---

## 16. Build modes and safety profiles

### 16.1 `dev_reference`

- host/reference model;
- rich diagnostics;
- dynamic test tooling permitted;
- sanitizers and assertions;
- no production signing.

### 16.2 `embedded_static`

- fixed arenas and embedded async;
- static controller/media profile;
- no heap in firmware paths;
- normal production type/AOP rules;
- runtime guards according to hardware.

### 16.3 `mission_critical`

- all paths statically complete for configured features;
- no unchecked `Any`, raw pointer, unknown FFI/assembly effect, dynamic loading, reflection, or silent fallback;
- bounded async/task/ring/timer/allocator receipts;
- locked access manifest and runtime protection;
- required formal properties and negative tests;
- deterministic failure policy;
- no test/emulator symbols;
- full evidence bundle.

### 16.4 `pool_allocable_mission_critical`

Permits runtime allocation only from certified fixed arenas with:

- typed generational handles;
- hard reservations and quotas;
- bounded allocation time;
- no general heap;
- no compaction/moving;
- retirement/wrap proof;
- pool health telemetry;
- admission analysis.

This should be the practical default for SSD firmware because command, DMA, media, and recovery contexts are naturally pooled.

---

## 17. Migration and implementation plan

### M0 — Freeze truth and classify existing paths

**Goal:** prevent further ambiguity between example, model, RTL endpoint, and production claims.

Work:

- add audited-status document generated from current tests/profiles;
- label each media backend by fidelity tier;
- label `fw/` as host/reference, `fw_rv32/` as scalar firmware floor, and FPGA RTL as `SimpleFpgaRv32` prototype;
- inventory every `fake/mock/stub/no-op/test hook/direct address` occurrence;
- capture current baseline evidence bundle;
- mark direct `.nandram` access as a temporary known violation with removal milestone;
- create source-origin/license ledger for external references.

Exit:

- no documentation calls the current stack a universal production SSD firmware;
- every existing test has an evidence grade and model tier;
- baseline behavior and performance are recorded.

### M1 — Seal boundaries and introduce AOP source rules

**Goal:** make new bypasses impossible while old code is migrated.

Work:

- define `MediaService`, `ControllerService`, `DmaService`, `AllocatorService` interfaces;
- move emulator/test APIs to test-only modules;
- make media and pool backing fields private/opaque;
- add source/dependency AOP policies;
- add compile-fail tests for imports/calls;
- replace silent emulator no-ops with absent capability or explicit `Unsupported` in test/reference builds;
- create production/test dependency graphs.

Exit:

- FTL cannot import NAND implementations;
- production graph cannot import test models;
- existing tests pass through adapters;
- all new source-level bypass negative tests fail correctly.

### M2 — Controller/media profile generator and full semantic types

**Goal:** remove duplicated constants and raw cross-domain integers.

Work:

- define profile schema and validator;
- import or hand-author initial `SimpleFpgaRv32` register description;
- generate linker/testbench/firmware constants from one profile;
- implement semantic types and checked constructors;
- convert NVMe wire decode to typed commands;
- convert NAND geometry and FTL mapping interfaces;
- convert queue, DMA, timer, and hardware types;
- add profile equation and illegal-composition tests.

Exit:

- no handwritten queue/memory/NAND geometry constant in migrated paths;
- LBA/PPN/queue/command/DMA types cannot be mixed without explicit unsafe conversion;
- `SimpleFpgaRv32` compiles from generated profile outputs.

### M3 — Fixed embedded async runtime and opaque allocators

**Goal:** replace dynamic/general Promise behavior in device paths.

Work:

- implement typed arenas, ownership transfer, generation retirement, quotas;
- implement embedded promise slots and lowering;
- implement event rings/timers/wakeups;
- build lane scheduler and admission credits;
- add reset/cancel/deadline epochs;
- generate memory receipts;
- formally/model-check arena, ring, and promise invariants.

Exit:

- device firmware uses no general Promise/list/callback runtime;
- no heap allocation in the profiled firmware path;
- all async operations have fixed state and pool bounds;
- current TaskPool backing arrays are no longer public.

### M4 — Refactor `SimpleFpgaRv32` as first certified profile

**Goal:** preserve current evidence while proving controller-neutral core separation.

Work:

- implement generated BSP for existing RV32/AXI model;
- move mailbox/queue/memory constants into profile;
- replace flattened source build with normal module/profile compilation;
- migrate NVMe command and FTL vertical slice: Identify, queue create, one read/write, completion;
- add DMA/controller service even if model is small;
- retain old path temporarily for differential comparison;
- measure code size, RAM, cycles, and regression behavior.

Exit:

- new and old paths agree on supported traces;
- no controller register/offset appears in FTL;
- normal module build replaces textual source rewriting for migrated code;
- profile reaches C2/C3 for its actual feature subset.

### M5 — Replace `.nandram` with typed test control and add IR access proof

**Goal:** close the user-requested direct-access gap.

Work:

- implement private T1 functional media model;
- add separate `MediaTestControl` endpoint;
- migrate GHDL and QEMU fault injection/snapshots;
- remove `_nandram_start/_end` ABI from test scripts;
- add typed HIR/MIR memory-effect pointcuts;
- generate access manifest and receipt;
- add link/relocation/disassembly verifier;
- implement runtime AXI/PMP protection tests where possible;
- expand negative corpus for helpers/generics/macros/FFI/asm.

Exit:

- repository tests contain no raw `.nandram` read/write path;
- zero unclassified media-model state access;
- all illegal-access tests reject/trap;
- production image has no test-control or model symbols.

### M6 — Cosmos+ real-NAND profile

**Goal:** prove the architecture on an independent real controller/media platform.

Work:

- create `CosmosPlusZynq7000` controller/board profile;
- create a lawful media profile for installed NAND;
- implement FMC/NAND/ECC/DMA/IRQ/timer/reset BSP;
- bring up discovery and conservative timing;
- run read/program/erase and bad-block tests;
- port FTL vertical slice, then recovery/journal;
- use pynvme/nvme-cli/blktests host harness;
- add JTAG/UART/PCIe lab automation and power control;
- maintain independent Cosmos firmware comparison where licensing permits.

Exit:

- profile reaches C4, then C5;
- real NAND operations use the same core interfaces as `SimpleFpgaRv32`;
- no controller-specific conditional enters core/FTL;
- full evidence bundle records board/media revisions.

### M7 — NVMe breadth and external differential testing

**Goal:** expand protocol support without weakening capability truthfulness.

Work:

- multiple I/O queues and concurrency;
- robust PRP, then SGL where supported;
- MSI/MSI-X profiles;
- Flush/durability behavior;
- logs/telemetry/health;
- reset, abort, error recovery;
- FEMU/NVMeVirt differential matrices;
- pynvme property/fuzz traces;
- Linux blktests and SPDK/fio performance.

Exit:

- every advertised feature has positive/negative/reset/fault evidence;
- malformed inputs cannot escape typed validation;
- no behavior depends on emulator-specific shortcut.

### M8 — Power-loss, recovery, reliability, and security

**Goal:** reach production SSD behavior rather than endpoint functionality.

Work:

- persistent journal/checkpoint format and versioning;
- systematic power-cut campaign;
- GC/wear/refresh/disturb/retention/read-retry;
- metadata redundancy and degraded/read-only modes;
- secure boot/update/rollback policy;
- debug/test capability removal and signing separation;
- DMA threat model and IOMMU/firewall enforcement;
- watchdog, fatal-error containment, forensic telemetry.

Exit:

- durability contract is tested at every operation phase;
- bounded recovery demonstrated;
- security/access manifests match runtime protection;
- real-media C5 campaigns pass.

### M9 — C6 production release process

**Goal:** make certification reproducible and reviewable.

Work:

- full source/toolchain/profile pinning;
- reproducible image and SBOM;
- proof/access/evidence receipts;
- independent review of unsafe boundaries, AOP policy, and generated profile;
- performance, endurance, thermal, and power campaigns;
- signed release and rollback image;
- field telemetry/update/recovery policy;
- revalidation triggers and supported-controller table.

Exit:

- zero production fake/mock/test symbols;
- zero direct/illegal access findings;
- all release gates and independent reviews complete;
- controller/media profile marked C6 with immutable evidence references.

---

## 18. Parallel workstreams and dependency order

| Workstream | Primary ownership | Can start | Blocks |
|---|---|---|---|
| W1 Current-state inventory/evidence | Firmware QA | Immediately | Reliable baseline and docs |
| W2 Profile schema/generator | Compiler + hardware | Immediately | Typed BSP, generated AOP facts |
| W3 Semantic types/wire decode | Language + NVMe | After initial schema shapes | Core migration |
| W4 AOP source/IR access verifier | Compiler/AOP | Source rules immediately; IR after region model | Direct-access closure |
| W5 Embedded async/lowering | Compiler/runtime | Immediately with agreed operation model | Device-path migration |
| W6 Typed arenas/rings | Runtime/formal | Immediately | Async and FTL admission |
| W7 Media service and models | NAND/reliability | After interface/types draft | Removal of old backend exposure |
| W8 Simple FPGA profile | RTL/firmware | After profile generator minimum | C3 certification |
| W9 Cosmos+ profile/HIL | Board/NAND | Hardware procurement/setup immediately; code after interfaces | C5 proof |
| W10 Host conformance/differential | QA/storage | Immediately against baseline; expand continuously | Release confidence |
| W11 Persistence/power loss | FTL/reliability | Model design immediately; implementation after async/allocator | C5/C6 |
| W12 Release/security/evidence | Security/release | Manifest design immediately | C6 |

Coordination rules:

- Interface and invariant documents are versioned before parallel implementation.
- Each workstream owns disjoint modules and generated boundaries.
- Cross-workstream changes use typed contracts, not direct field access.
- A higher-level integration agent reviews capability truthfulness and shortcut findings.
- No workstream may temporarily expose private backing state to "unblock testing"; use a test-control adapter.

---

## 19. Acceptance criteria

### 19.1 Architecture

- reusable core no longer lives only under `examples/`;
- controller and media profiles are independent and statically composed;
- FTL/reliability depend only on typed services;
- unsupported features are absent or explicit, never no-op success;
- controller-specific constants are generated.

### 19.2 Types

- all public firmware interfaces use semantic fixed-width/bounded types;
- wire integers are validated once;
- compile-fail tests prove LBA/PPN, queue/command, byte/block, and pool/handle separation;
- runtime-discovered geometry cannot exceed compiled maxima;
- no sentinel integer represents absence/error in new APIs.

### 19.3 Async and allocation

- no general heap or host Promise in device dependency closure;
- all task/promise/ring/timer pools are fixed and reported;
- hard-real-time reserves are provable;
- stale/forged/cross-pool/cross-owner handles are rejected;
- generation wrap cannot recreate a valid key;
- cancellation/reset late completions cannot mutate new state.

### 19.4 NAND and emulator

- full-page/OOB T1 model exists;
- real backend exists for at least one C5 profile;
- emulator/model state is opaque;
- all fault injection uses typed test control;
- all observability is immutable/summary based;
- no raw `.nandram` offset ABI remains;
- production image contains no model/test-control state or symbols.

### 19.5 AOP/access proof

- source dependency graph has no forbidden edge;
- typed IR classifies every external effect and protected-region access;
- link/relocation/section verifier passes;
- all negative-access tests fail/trap for intended reason;
- runtime protection matches manifest where hardware supports it;
- access receipt is bound to image hash.

### 19.6 Automation/evidence

- PR, nightly, and release matrices are implemented;
- external differential tests run deterministically;
- RTL and HIL use typed control, not direct state mutation;
- shortcut detector findings are all classified;
- critical mutation suite is killed;
- evidence bundle is reproducible and immutable;
- advertised NVMe capabilities match certified evidence.

---

## 20. Risk register

| Risk | Likelihood | Impact | Mitigation | Release trigger |
|---|---:|---:|---|---|
| "All controllers" expands into undocumented proprietary targets | High | High | Define profile contract/certification; require lawful docs and BSP. | Reject unsupported target claim. |
| AOP call rules miss raw/helper/FFI accesses | High | Critical | Typed IR provenance, link verifier, runtime firewall, negative corpus. | Zero unclassified effects/accesses. |
| Profile abstraction adds hot-path overhead | Medium | High | Static specialization/monomorphization; measure assembly/cycles. | No unapproved regression versus profile-specific baseline. |
| Type wrappers remain unrestricted raw integers | Medium | High | Private constructors, bounded generated types, compile-fail tests. | Public APIs contain no raw cross-domain IDs. |
| Embedded async deadlocks due to partial resource acquisition | Medium | Critical | Full admission or proven acquisition order; model checking. | Deadlock freedom for certified operation graph. |
| Pool generation exhaustion/retirement reduces service capacity | Low/medium | High | Lifetime calculation, wide generations, retired-slot reserve/telemetry. | Required service life and minimum reserve proved. |
| Late hardware completion corrupts reused slot | Medium | Critical | Generation + controller/media epoch checks; drain/reset rules. | Stale-completion negative tests pass. |
| Test model becomes de facto production backend | High | High | Separate dependency graph, signing, symbols, evidence labels. | Production image has zero model/test symbols. |
| One-word media model overstates reliability coverage | High | High | Fidelity-tier labels and full-page model gate. | C5 claims require real media; no tier substitution. |
| Same implementation acts as oracle | Medium | High | Independent reference models/spec vectors/external tools. | Critical properties have independent oracle. |
| Cosmos+ toolchain/hardware age blocks reproducibility | Medium | Medium/high | Containerized/pinned tools where licensing permits; second real board later. | C5 evidence reproducible on maintained lab image. |
| External project licensing prevents source reuse | Medium | High | Architecture-only reuse by default; SPDX/source ledger. | Legal review before copied code enters tree. |
| Vendor NAND details unavailable | High | High | Use documented media only; explicit unknown-media fail/read-only policy. | No heuristic unsupported-media production mode. |
| Formal proof diverges from implementation/generated constants | Medium | Critical | Generate proof parameters; bind hashes; mutation checks. | Proof receipt matches image/profile hash. |
| CI becomes too slow and is bypassed | Medium | High | Fast affected subset, nightly full matrix, release lab queue, failure-first scheduling. | Required gates cannot be manually waived without signed exception. |
| Hardware protection unavailable on minimal core | High for prototype | High | Make AXI firewall/static proof mandatory; add PMP/Smepmp roadmap. | Profile certification states residual protection level. |
| Power-cut tests damage or confuse lab devices | Medium | High | Disposable inventory, automated serial/board identity, isolated power control. | Lab orchestration verifies exact target before destructive action. |
| Silent unsupported behavior enters Identify/logs | Medium | High | Generated capabilities from certification record. | Identify field-to-test traceability complete. |
| Source flattening/text rewrite creates semantic drift | Medium | High | Migrate to normal module/profile compiler pipeline; differential build. | No textual type/source rewrite in certified path. |
| Test hooks remain reachable through generic/unused code | Medium | Critical | Whole-program dependency/link/effect analysis under LTO. | Zero forbidden symbols/relocations after final link. |

---

## 21. Rejected alternatives

### 21.1 One giant `Controller` interface with optional methods

Rejected because optional methods tend to become no-ops or runtime `if` chains, retain test code, and hide required capabilities. Use small capability interfaces and static composition.

### 21.2 Universal firmware binary with runtime plug-ins

Rejected for embedded production because it increases attack surface, memory, dynamic dispatch, incomplete-path risk, and proof state. Optional multi-board images use a closed precompiled set selected once at boot.

### 21.3 AOP only at source import/call level

Rejected because memory, FFI, inline assembly, generated code, and indirect references can bypass it. Use whole-program typed effects plus binary/runtime checks.

### 21.4 Runtime bounds checks on raw `i64` everywhere

Rejected because it cannot prevent domain confusion and repeats work. Validate wire values once into semantic bounded types.

### 21.5 General heap plus "do not allocate in hot path" convention

Rejected because it is difficult to prove, fragments memory, and invites hidden allocation through libraries. Use fixed typed arenas and compiler dependency checks.

### 21.6 General Promise/callback runtime on device

Rejected because callback lists, closure state, dynamic chaining, and unbounded combinators are incompatible with deterministic embedded firmware. Use explicit fixed async state machines.

### 21.7 Direct emulator memory access because "tests are trusted"

Rejected because it bypasses the same boundary the test is meant to validate, couples tests to layout, survives unnoticed into engineering images, and cannot be transferred to real hardware. Use typed test control and immutable snapshots.

### 21.8 Treating an NVMe endpoint as proof of an SSD

Rejected. Endpoint/front-end, FTL, media controller, NAND model, and real NAND are separate evidence dimensions.

---

## 22. First implementation slices

The following vertical slices minimize risk and produce useful evidence early.

### Slice A — Read-only Identify path

```text
host SQE -> typed DMA fetch -> typed admin decode -> generated Identify data
-> typed completion -> CQ DMA -> host validation
```

Gates:

- no raw MMIO outside controller service;
- profile-generated BAR/queue constants;
- no heap;
- promise/arena IDs used end to end;
- pynvme/nvme-cli comparison;
- reset during each state;
- stale completion rejection.

### Slice B — One-page write/read through T1 model

```text
validated write -> admission -> DMA buffer lease -> FTL mapping transaction
-> MediaService program -> journal commit -> completion
validated read -> mapping lookup -> MediaService read/ECC -> DMA out -> completion
```

Gates:

- full page/OOB model, not scalar;
- test faults through `MediaTestControl` only;
- direct model-state access negative tests;
- power cut before/after journal/data/mapping states;
- independent mapping oracle.

### Slice C — Existing RV32 RTL migration

Run Slice A/B against `SimpleFpgaRv32` using the existing firmware-in-loop infrastructure, replacing the raw `.nandram` interface. Differentially compare old and new traces for the supported subset.

### Slice D — Cosmos+ single-channel bring-up

Start with one channel/target under conservative timing and polling. Prove discovery, page read/program/erase, ECC, and bad-block behavior before enabling all channels, interrupts, or performance features.

### Slice E — Multi-queue and media parallelism

After correctness, add queue pairs, DMA concurrency, channel schedulers, and MSI-X by increasing profile limits and proving resource/admission invariants.

---

## 23. Detailed review checklist

### 23.1 Controller/BSP review

- Are all registers generated and typed?
- Are reserved bits masked and access modes enforced?
- Are all MMIO accesses ordered correctly?
- Are reset defaults and reset completion checked?
- Are DMA windows, address widths, and cache rules explicit?
- Can the device DMA outside approved host/local ranges?
- Are interrupts acknowledged without losing events?
- Are watchdog, timeout, and fatal-error paths deterministic?
- Are debug/test registers absent or locked in production?
- Does runtime protection match the access manifest?

### 23.2 NVMe review

- Does each command validate reserved bits and namespace/range?
- Are PRP/SGL chains bounded, aligned, cycle-safe, and overflow-safe?
- Does completion occur only at the declared data/durability point?
- Are queue phase/head/tail rules correct across wrap/reset?
- Are duplicate and stale `(qid,cid,epoch)` completions impossible?
- Are Identify/log fields generated from certified capabilities?
- Are unsupported commands returned accurately?
- Do controller reset, subsystem reset, link-down, and abort drain resources?

### 23.3 FTL/recovery review

- Is mapping update atomic under the durability contract?
- Is the old mapping retained until the new page is safely committed?
- Are orphan pages and torn metadata detected?
- Is replay idempotent and bounded?
- Can bad-block failure occur at every metadata/data phase?
- Are GC, refresh, and foreground writes deadlock-free?
- Are sequence/epoch counters protected against wrap?
- Does recovery avoid trusting unauthenticated/corrupt metadata?

### 23.4 NAND/reliability review

- Is parameter-page identification validated?
- Is geometry profile-bound and discovered safely?
- Is full page/OOB/codeword behavior used for production evidence?
- Are factory-bad markers preserved?
- Are program order and partial-program constraints enforced?
- Are ECC and erased-page semantics independently tested?
- Is read-retry real for the backend or explicitly unsupported?
- Are timing/training and timeout failures contained per channel/LUN?
- Are wear, retention, disturb, and refresh policies observable?

### 23.5 Async/allocator review

- Does the operation reserve sufficient resources before mutation?
- Is every await point represented in the memory receipt?
- Can cancellation/timeout release a resource still used by hardware?
- Can an ISR or late event use a stale generation/epoch?
- Is every ring full policy safe?
- Can background work consume hard-reserved slots?
- Are pool arrays opaque and all dereferences validated?
- Is generation retirement/lifetime capacity proved?

### 23.6 AOP/access review

- Does policy cover expanded macros/generics?
- Are FFI and inline assembly effects complete?
- Are every protected-region load/store and hardware effect classified?
- Are linker sections/symbols/relocations clean?
- Can a function pointer or dynamic resolver reach a forbidden target?
- Does the production image contain model/test-control code?
- Do negative tests fail for the intended diagnostic?
- Does hardware protection trap a deliberately injected bypass?

### 23.7 Fake/shortcut review

- Is any success path constant or empty?
- Is a simplified model labeled by fidelity tier?
- Does a test hook appear on a production object?
- Is a feature advertised without certification evidence?
- Is the oracle independent?
- Are TODO/no-op/fallback findings classified?
- Does release link include a fake/mock/stub/test library?

---

## 24. Requirements-to-evidence traceability

| Requirement | Design mechanism | Primary tests/evidence |
|---|---|---|
| Support documented controllers | Static `ControllerProfile` + BSP contract | Profile validation, compile matrix, C0–C6 record |
| Controller/media independence | Separate controller/media/board profiles | Illegal composition compile tests; two independent profiles |
| Fully typed parameters | Semantic bounded/profile-bound types | Compile-fail domain-mixing tests; wire decode property tests |
| Highly adaptable | Generated profiles/importers; runtime narrowing | Profile matrix; no hot-path dynamic dispatch regression |
| Full embedded Promise async | Fixed slot state machines and typed IDs | Memory receipt, transition model check, timeout/reset tests |
| Index pointers/allocator | Opaque generational arenas and ownership transfer | ABA/stale/owner/formal tests; lifetime capacity proof |
| Real NAND path | `NandPort` real backend and C5 profile | Parameter-page, full-page, ECC, bad block, power HIL |
| No direct emulator access | Opaque model + `MediaTestControl` | Negative access corpus; no `.nandram`; access receipt |
| AOP verifies illegal access | Source + IR + link + runtime policy | Zero unclassified effects, linker checks, firewall trap |
| No fake/mock shortcuts | Test-only graph, semantic lint, binary denylist | Classified findings, mutation kill set, symbol report |
| Honest capability advertising | Generated Identify/log data from certification | Field-to-test traceability, host conformance |
| Production reproducibility | Evidence bundle, pinned tools/profile | Rebuild/hash match, SBOM, signatures |

---

## 25. Source inventory

### 25.1 Audited Simple sources

All links below are pinned to the audited revision.

- Repository revision: <https://github.com/ormastes/simple/commit/0fce018eda368724ab9650aa8af1207c3f9179ce>
- Embedded overview: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/README.md>
- NVMe firmware top-level README: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/README.md>
- Firmware/reference README: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/README.md>
- Production status: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md>
- RV32 firmware README: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw_rv32/README.md>
- RV32 build script: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs>
- RV32 boot script: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs>
- Minimal RV32 NVMe/AXI endpoint: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/fpga_riscv/rtl/rv32_nvme_axi.vhd>
- Firmware-in-loop testbench: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/fpga_riscv/rtl/tb_rv32_nvme_fw_in_loop.vhd>
- GHDL firmware-in-loop script: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/scripts/fpga/ghdl_rv32_nvme_fw_in_loop.shs>
- Recovery automation: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/scripts/check/check-rv32-nvme-nand-recovery.shs>
- QEMU host-parity script: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs>
- FIL composition: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fil.spl>
- FMC/backend dispatch and test hooks: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fil_fmc.spl>
- Behavioral NAND model: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fil_nand.spl>
- ONFI-shaped NAND device model: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fil_nand_device.spl>
- Vt/reliability NAND emulator: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fil_nand_emu.spl>
- NAND semantic wrappers: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/nd_types.spl>
- Generation task pool: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/examples/09_embedded/simpleos_nvme_fw/fw/fw_pool.spl>
- General Promise implementation: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/src/compiler_rust/lib/std/src/concurrency/promise.spl>
- Current AOP requirement: <https://github.com/ormastes/simple/blob/0fce018eda368724ab9650aa8af1207c3f9179ce/doc/02_requirements/language/aop/aop.md>

### 25.2 Open-source/source-available SSD and NVMe projects

- Cosmos+ OpenSSD: <https://github.com/Cosmos-OpenSSD/Cosmos-plus-OpenSSD>
- Jasmine OpenSSD: <https://github.com/openssd/jasmine>
- Cosmos+ firmware with CI (`ocp-fw`): <https://github.com/freshLiver/ocp-fw>
- OCSSD-plus: <https://github.com/Cosmos-OpenSSD/OCSSD-plus>
- OX controller: <https://github.com/DFC-OpenSource/ox-ctrl>
- Portable NVMe CSD: <https://github.com/rick-heig/nvme_csd>
- OpenExpress paper/project page: <https://www.usenix.org/conference/atc20/presentation/jung>
- NVMeCHA: <https://github.com/yhqiu16/NVMeCHA>
- Lambda-IO: <https://github.com/thustorage/lambda-io>
- PNVMe project description: <https://jacen.li/projects/pnvme/>
- FEMU: <https://github.com/MoatLab/FEMU>
- NVMeVirt: <https://github.com/snu-csl/nvmevirt>
- SimpleSSD FullSystem: <https://github.com/SimpleSSD/SimpleSSD-FullSystem>
- pynvme: <https://github.com/pynvme/pynvme>
- Linux blktests: <https://github.com/linux-blktests/blktests>
- OpenFlash Controller Lab: <https://github.com/manishklach/openflash-controller-lab>
- Example of a host/root FPGA NVMe controller that must not be classified as SSD firmware: <https://github.com/mcrl/NVMe>

### 25.3 Standards and architecture references

- NVM Express Base/2.4 specification page: <https://nvmexpress.org/specification/nvm-express-base-specification/>
- NVM Express specification set: <https://nvmexpress.org/specifications/>
- PCI-SIG PCIe 7.0 v1.0 announcement: <https://pcisig.com/specifications/pcie-70-specification-version-03-now-available-members>
- PCI-SIG PCIe 8.0 v0.3 development status: <https://pcisig.com/blog/pcie-80-specification-version-03-now-available-members>
- ONFI 5.2 feature/status reference (secondary; verify against acquired normative specification): <https://community.cadence.com/cadence_blogs_8/b/fv/posts/onfi-5-2-what-s-new-in-open-nand-flash-interface-s-latest-5-2-standard>
- Accellera SystemRDL: <https://www.accellera.org/downloads/standards/systemrdl>
- IEEE 1685-2022 IP-XACT: <https://standards.ieee.org/ieee/1685/10583/>
- CMSIS-SVD specification: <https://open-cmsis-pack.github.io/svd-spec/main/index.html>
- Embassy embedded executor: <https://docs.embassy.dev/embassy-executor/git/std/index.html>
- RISC-V privileged architecture/PMP: <https://docs.riscv.org/reference/isa/priv/machine.html>
- RISC-V Smepmp: <https://docs.riscv.org/reference/isa/v20260120/priv/smepmp.html>
- seL4 capDL: <https://docs.sel4.systems/projects/capdl/index.html>
- Generational arena/ABA reference: <https://docs.rs/generational-arena/latest/generational_arena/>
- Generation-wrap/key-retirement reference: <https://docs.rs/slotmap-careful/latest/slotmap_careful/>

---

## 26. Final recommended order of decisions

1. Approve the meaning of "all controllers" as certified documented profiles.
2. Approve the split between controller, media, and board profiles.
3. Approve AOP as the verifier—not the NAND abstraction—and fund typed-IR access pointcuts.
4. Approve separate embedded Promise/async and typed-arena runtimes.
5. Approve the removal of direct `.nandram` access and replacement with typed test control.
6. Approve `SimpleFpgaRv32` as the first refactor/certification profile.
7. Approve Cosmos+ or another documented real-NAND board as the first C5 target.
8. Approve the capability/evidence model that prevents unsupported features from being advertised.
9. Approve the move of reusable firmware out of `examples/` while retaining thin demos.
10. Begin M0–M3 in parallel, with M4/M5 as the first integrated delivery and M6 as the first real-media proof.

The key success criterion is not the number of controllers named in a table. It is that adding the next controller requires only a profile/BSP/media implementation and evidence—without changing the typed NVMe, FTL, reliability, async, allocator, or access-policy core.
