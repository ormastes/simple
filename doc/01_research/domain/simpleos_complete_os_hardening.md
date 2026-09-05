<!-- codex-research -->
# Domain Research: SimpleOS Complete OS Hardening

## Filesystems and executable trust

- The [UEFI 2.10 FAT protocol definition](https://uefi.org/specs/UEFI/2.10/13_Protocols_Media_Access.html) defines a stable interoperable EFI FAT subset, BPB-derived layout, FAT12/16/32 behavior, long filenames, case-insensitive directory uniqueness, UCS-2 handling, and FAT32 data-region alignment. SimpleOS should select and test an explicit FAT32 profile rather than infer compatibility from mounting one image.
- Microsoft documents FAT32's 4 GiB file-size ceiling and lack of journaling/change logs in its [filesystem comparison](https://learn.microsoft.com/en-us/windows/win32/fileio/filesystem-functionality-comparison). Duplicate FAT copies provide damage tolerance, not transactional durability.
- POSIX [`fsync()`](https://pubs.opengroup.org/onlinepubs/009695399/functions/fsync.html) and [`close()`](https://pubs.opengroup.org/onlinepubs/009604499/functions/close.html) distinguish requested persistence from delayed I/O errors; a conformance contract must say what flush commits and which errors can arrive later.
- The [Linux VFS contract](https://docs.kernel.org/filesystems/vfs.html) demonstrates one shared pathname/open/stat/read/write/fsync layer over backend-specific superblock, inode, dentry, and file operations. POSIX [pathname resolution](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html) supplies traversal and error semantics worth adopting selectively.
- DBFS and NVFS are project-specific names; no external standard determines their behavior. Their guarantees must be defined by SimpleOS requirements and conformance tests.
- Linux [fs-verity](https://docs.kernel.org/filesystems/fsverity.html), UEFI [Secure Boot](https://uefi.org/specs/UEFI/2.11/32_Secure_Boot_and_Driver_Signing.html), and [NIST SP 800-193](https://csrc.nist.gov/pubs/sp/800/193/final) separate integrity, authentication, and recovery. Executable loading should validate the open file's format/ISA/ranges, apply mount execution policy, avoid pathname TOCTOU, and authenticate privileged payloads when the selected profile requires it.

## LLVM/Clang target-native porting

- Clang's [cross-compilation guide](https://clang.llvm.org/docs/CrossCompilation.html) requires an explicit target triple and explains why CPU flags alone can still produce host code. The triple, sysroot layout, include/library search, assembler, and linker must agree.
- LLVM's [code generator documentation](https://llvm.org/docs/CodeGenerator.html) identifies the backend responsibilities: data layout, instruction selection, assembly/disassembly, relocations, calling convention, object writing, and target ABI.
- The [System V ELF ABI](https://refspecs.linuxfoundation.org/elf/gabi41.pdf), [Arm ABI](https://github.com/ARM-software/abi-aa), and [RISC-V ELF psABI](https://github.com/riscv-non-isa/riscv-elf-psabi-doc) define common and architecture-specific executable/calling conventions.
- Clang's [toolchain documentation](https://clang.llvm.org/docs/Toolchain.html) and LLVM libc's [full cross-build guide](https://libc.llvm.org/full_cross_build.html) show that a usable target environment needs headers, libc/OS runtime, startup objects, compiler runtime, libraries, linker, and loader conventions—not only a frontend executable.
- LLVM's [cross-compile LLVM guide](https://llvm.org/docs/HowToCrossCompileLLVM.html) explicitly separates host build tools, target triple/sysroot, and install prefix. Staging a target artifact is therefore evidence of construction only; target-native acceptance begins when the compiler and linker themselves execute inside the guest.
- QEMU documents x86, Arm, and RISC-V [system emulation](https://www.qemu.org/docs/master/about/emulation.html). Such receipts must be labeled emulated unless an applicable KVM/HVF/WHPX accelerator is recorded.

## HTTP, SSH, and database protocol claims

- HTTP semantics and fields are defined by [RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html); HTTP/1.1 framing is [RFC 9112](https://www.rfc-editor.org/rfc/rfc9112.html). Servers must parse messages as octets, reject ambiguous framing and whitespace-before-colon, define field/body limits, and close or error safely rather than ignore oversized input.
- HTTP/2 is [RFC 9113](https://www.rfc-editor.org/rfc/rfc9113.html). A supported profile needs ALPN/prior-knowledge handling, SETTINGS and header-list bounds, connection/stream flow control, concurrency limits, and bounded multiplexed buffering.
- HTTP/3 is [RFC 9114](https://www.rfc-editor.org/rfc/rfc9114.html) over QUIC [RFC 9000](https://www.rfc-editor.org/rfc/rfc9000.html). Framing/QPACK without QUIC transport, flow control, stream lifecycle, retransmission, and congestion control is not HTTP/3 server support.
- SSH's architecture is split across transport, user authentication, and connection layers by [RFC 4251](https://www.rfc-editor.org/rfc/rfc4251.html), [RFC 4253](https://www.rfc-editor.org/rfc/rfc4253.html), [RFC 4252](https://www.rfc-editor.org/rfc/rfc4252.html), and [RFC 4254](https://www.rfc-editor.org/rfc/rfc4254.html). Packet allocation, auth attempts/time, channels, windows, output buffers, and rekey must be bounded.
- Current SSH algorithm guidance is [RFC 9142](https://www.rfc-editor.org/rfc/rfc9142.html); extension discovery is [RFC 8308](https://www.rfc-editor.org/rfc/rfc8308.html). Unsupported or weak algorithms must not appear through silent downgrade.
- There is no generic standards-defined “database protocol.” Requirements must name a concrete protocol/profile, framing, transport/TLS/ALPN, authentication, operations, transaction semantics, extensions, and limits. Unknown mandatory capabilities fail closed; [RFC 6709](https://www.rfc-editor.org/rfc/rfc6709.html) provides general extension-design guidance and [RFC 7301](https://www.rfc-editor.org/rfc/rfc7301.html) covers ALPN.

## Window management, cross-architecture evidence, and performance

- UEFI's [architecture-independent model](https://uefi.org/specs/UEFI/2.10/02_Overview.html) requires a claimed conformance profile to implement its required semantics. An architecture matrix should reuse identical behavioral test IDs while binding each receipt to the architecture-specific image and firmware path.
- [EWMH 1.5](https://specifications.freedesktop.org/wm/latest-single/) and the [Wayland protocol](https://wayland.freedesktop.org/docs/html/) are useful behavior inventories for mapping, focus, stacking, resize/configure ordering, input, outputs, buffers, and presentation. They are not automatically SimpleOS compatibility requirements; compatibility must be selected explicitly.
- LLVM's [benchmarking guidance](https://llvm.org/docs/Benchmarking.html) recommends repeated runs, high-resolution timing, controlled CPU/services/frequency, explicit noise analysis, and careful interpretation. The [LLVM test suite](https://llvm.org/docs/TestSuiteGuide.html) separates correctness from runtime, compile-time, and size metrics.
- Performance evidence should retain fixed fixture/configuration, warmup, raw samples, p50/p95/max or other selected aggregates, environment metadata, binary hashes, and a variance rule. A single timing marker is not a regression baseline.
- Duplication gates should distinguish intentional adapters from competing canonical owners. Every exception needs an owner, rationale, quantified maintenance/performance impact, and removal condition.

## Domain implications for requirement selection

1. Choose a concrete FAT32 compatibility and durability profile; specify DBFS/NVFS guarantees locally.
2. Choose whether filesystem execution defaults to trusted mounts, explicit `exec`, or authenticated-only payloads.
3. Define target-native toolchain acceptance as guest execution plus guest compile/link/run, never staging.
4. Select exact HTTP, SSH, and database protocol profiles; “all protocols” is not independently testable without a manifest.
5. Select whether WM requirements are SimpleOS-native only or include an EWMH/Wayland compatibility profile.
6. Select quantitative performance, robustness, duplication, and evidence thresholds before design.

