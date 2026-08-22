# Architecture: SimpleOS filesystem toolchain and servers

## Decision

Keep one owner per boundary:

```text
QEMU request -> boot TCP facade -> HTTP default or POST /db service
mounted VFS file -> executable range reader -> ELF PT_LOAD mapper -> user task
target Simple payload -> install image role list -> compiler/interpreter/loader paths
```

The loader opens the requested canonical path, reads the ELF header/program
headers, allocates pages, and fills each `PT_LOAD` range with bounded reads. It
does not cache or substitute executable bytes; the old global preload is outside
the hosted launch path.

The existing single HTTP listener remains the only network owner. `POST /db`
dispatches to one persistent bounded database service; all other requests keep
the existing HTTP response path. A second listener and scheduler are unnecessary
for the selected request/response proof.

The DB scenario uses existing Pure Simple parsing/storage primitives where the
freestanding closure supports them; otherwise its smallest owner-layer service
implements only the selected bounded create/insert/select protocol and is not
presented as the full historical `simple_db` product.

GOT residency remains an explicit bare-metal optimization. Hosted SimpleOS,
Clang, Simple compiler, interpreter, and loader all use filesystem provenance.
## Restart12 deployment admission boundary (2026-08-14)

The x86_64 lane has two non-circular admission records: the image-embedded
`simpleos_toolchain_deployment_manifest` owns component identity, while the
pre-boot external `simpleos_toolchain_image_admission_receipt` owns the closed
image and kernel hashes. Post-boot
`simpleos_toolchain_desktop_guest_receipt` owns firmware, boot argv, desktop,
framebuffer and guest execution evidence. The combined owner keeps one
`gui_entry_desktop.spl` QEMU lifetime through desktop evidence and guest
toolchain execution. Exact schemas and boundaries are frozen in
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

<!-- codex-architecture -->
## Wave 4 owner convergence (2026-08-21)

The filesystem launch path now has explicit, bounded owners rather than one
architecture-sized compatibility unit:

```text
boot block owner -> mounted FAT32 value -> MountTable publication
NVMe lease owner -> positioned DirectIo -> VFS dispatch/write owners
execute-open authority -> authenticated media parser -> ISA adoption owner
```

`src/os/kernel/fs/_Fat32Filesystem/` owns FAT mount/read, directory, allocation,
and write behavior behind the public `Fat32Filesystem` facade. The boot owner
retains the same mutable filesystem value across `mount` and publication; a
temporary copy cannot publish stale mount state. NVMe DMA allocation, the boot
runtime owner, positioned filesystem I/O, and Q35 lease/performance accounting
are likewise separate bounded owners. `MountTable`/VFS remains the shared
dispatch boundary; FAT32, DBFS, and NVFS do not acquire private executable
launchers.

x86_64, AArch64, and RV64 server images select architecture-specific entry
adapters, but all three require an execute-open binding, canonical signed
manifest material, pinned trust configuration, loader-issued adoption, and
scheduler collection. The former path-only spawn/capture facades are not an
authorization fallback. This is a source and construction contract until a
fresh QEMU run identifies the exact kernel, image, payload, mounted path,
request/response transcript, and exit oracle.

Large RV64 ELF loading is streamed from FAT in bounded ranges with a monotonic
cluster cursor, bounded FAT-chain transitions, aggregate `PT_LOAD` limits,
W^X checks, page-arena rollback, and no fixed whole-ELF buffer. The legacy
unauthenticated executor returns a rejection and the production entry reports
`missing-loader-authority-token`; it may not silently run the old path.

Per-architecture C runtime shims are decomposed into units below 800 lines and
linked with exactly one owner for scheduler, collection, network, topology, and
dynamic-value helpers. `src/app/simpleos_tool/main.spl` remains the single
compiler/interpreter/loader entry for the x86_64, AArch64, and RV64 builders;
architecture scripts vary only target/sysroot/link details and require an
admitted self-hosted builder. Artifact construction is not filesystem launch.

The guest LLVM provisioner admits target-matched static Clang, LLD, llvm-ar,
CRT, runtime, libc, and linker-script bytes and writes a construction receipt
whose `execution_claim` is false. A real x86_64 SimpleOS clang-20/LLD/llvm-ar
artifact set exists under `build/os/llvm/cross-x86_64-unknown-simpleos/bin` and
is static `ET_EXEC` without `PT_INTERP`, `DT_NEEDED`, or unresolved symbols.
That structural result is not a guest compile/link/run PASS; ARM64/RV64 LLVM
artifacts and every live hello-world row remain separately gated.

## Compiler/filesystem guest evidence owner (2026-08-22)

The six-ISA matrix now has one architecture-neutral validation boundary before
any serial PASS can be emitted. Architecture adapters collect actual VFS reads
and process results; `compiler_filesystem_guest_workflow_v2` validates the
ordered 13-role alias set, byte identity, image/nonce binding, exact interpreter
and native-compile commands, artifact reread, and exact hello output. Only then
does `compiler_filesystem_guest_protocol_v2` render the host parser's protocol.

The workflow buffers all records and returns zero lines on any mismatch. It
does not turn existing ARM/RISC-V VFS-presence probes into execution evidence.
Those architectures remain blocked until their adapters supply real observed
process results and authenticated fw_cfg metadata. The role catalog is
function-local because freestanding images do not execute module initializers.
