# SOSIX parallel QEMU completion audit

**Status:** active; release gate is not satisfied

**Authoritative matrix verdict (audited 2026-08-12):** `PASS 0 / BLOCKED 24`.
The exact per-cell TODO, owners, reviewers, and resume commands are maintained
in `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md` under
“Authoritative 24-cell completion TODO”. The immutable evidence source is
`matrix-v1-3efab06786847296`; later ARM64 diagnostic logs are also non-PASS.

This audit maps the selected requirements to the evidence that would prove the
full objective. Diagnostic runs are intentionally not promoted to release
PASS when compiler lineage, run correlation, firmware, or actual-host identity
is absent.

| Requirement | Current evidence | Verdict | Remaining proof |
|---|---|---|---|
| REQ-SQ-001 | shared settings resolver, host admission, six guest selectors | implemented | native-host consumption receipts |
| REQ-SQ-002 | typed operation/completion, FS codec, pump, wait set, owned-copy IPC | partial | real backend/client integration and pure-Simple tests |
| REQ-SQ-003 | 24-cell contract, collector, Linux rows, macOS postponements, and retained Windows/FreeBSD non-PASS bundles | partial | native Windows and FreeBSD execution; macOS remains explicitly postponed |
| REQ-SQ-004 | all six guest descriptors and system-test lanes | implemented | ARM64 runtime repair proof |
| REQ-SQ-005 | six descriptors and collector rows now require explicit firmware identity/mode; retained diagnostic serial logs expose implicit-default, direct-kernel, `-bios none`, and unresolved OpenSBI modes | not proven | resolved firmware path/version/hash and boot-stage correlation plus source/run nonce per PASS guest |
| REQ-SQ-006 | Linux diagnostic FAT listings for five guests | partial | ARM64 and all required actual-host rows |
| REQ-SQ-007 | ARM64 real mounted-payload/EL0/SVC/exit contract is implemented and its focused static spec is PASS 10/10; RV64 mounted-byte/user-ecall/exit/reap wiring is restored; ARM32 authenticated User/SVC/parent-reap owners and canonical mounted entry are implemented with static/ARM syntax evidence; x86_64 scheduler-token/CR3/exit/reap wiring is restored; RV32 and x86_32 remain live-blocked | partial, no live proof | build the restored ARM32/RV64/x86_64 slices with the frozen production compiler; implement RV32 Sv32 and x86_32 CPL3 live entry; retain mounted identity, target stdout, actual rc/reap, sabotage, and fresh QEMU evidence for every required row |
| REQ-SQ-008 | matrix rows now carry an explicit `compiler_in_filesystem` designation plus separate version and hello evidence paths; no collected row currently designates itself compiler-bearing | missing | designate only rows whose selected image embeds a qualified target-native payload, then retain in-guest version, compile, and run transcripts for each such host/guest cell |
| REQ-SQ-009 | setup/check/run scripts, shared guide, skill/wiki updates | implemented | native Windows PowerShell execution evidence |
| REQ-SQ-010 | OFD sequencer, fail-closed positioned read/write seams, no seek/I/O/restore compatibility emulation, and explicit value-threaded kernel install/dispatch state for registered-buffer syscall IDs 134/135; the dispatch owner is now the single registry/token policy owner and the kernel publishes its result directly | partial | obtain executable 3/3 owner and 4/4 kernel evidence with a usable pure-Simple CLI (three current attempts timed out before scenarios), classify or fix any remaining nested-owner persistence defect, then install through a production trap-runtime lifecycle owner and add integrated async backend plus errno/offset executable tests |
| REQ-SQ-011 | closed-schema immutable collector, clean commit/tree and transcript nonce correlation, compiler/firmware validation, and immutable 24-row all-blocked manifest `matrix-v1-3efab06786847296` | partial | replace blocked cells with authoritative PASS receipts after native reruns |
| REQ-SQ-012 | six macOS postponement bundles with resume commands | implemented | stays non-PASS until native execution |
| REQ-SQ-013 | configurable storage root and `/mnt/data/.simple` host config | implemented | external-host settings receipts |
| REQ-SQ-014 | typed host/display/input/configuration contracts, headless adapter, synchronous SDL2 compatibility adapter, hosted input callback adapter, SOSIX timer-based frame pacing, and snapshot-based Engine2D backend/transfer selection | partial | Win32/Cocoa/X11/Wayland/SimpleOS display producers, true asynchronous presentation fences, and remaining browser/device/evidence host consumers |
| REQ-SQ-015 | async core and notification wait adapter | partial | live VFS client/service path and compatibility integration |

The implementation-level PASS/RED audit and exact focused resume commands are
maintained in the authoritative agent plan under “SOSIX implementation
acceptance TODO”. The architecture-neutral explicit lifecycle state for
registered-buffer syscalls 134/135 now exists without globals, addresses, or
seek emulation. The kernel no longer duplicates token advancement or rebuilds
the returned registry owner: `positioned_dispatch_owner_v1` is the sole
transition policy. Earlier evidence remains RED at 2/4, and three subsequent
bounded commands timed out during compiler/test-runner startup before scenario
execution. The next owner must obtain fresh-session 3/3 and 4/4 focused PASS
before wiring that state into a production trap runtime. QEMU, ARM-specific,
and compiler files remain explicitly outside that work order.

## QEMU guest audit on this Linux host

| Guest | Boot + mount + real `ls` + filesystem program | Release status |
|---|---|---|
| x86_32 | fresh diagnostic boot + nonce + complete `/SYS/APPS` listing + filesystem probe markers retained | not a matrix PASS: bundle has only image/serial hashes, not admitted compiler/kernel lineage, clean source identity, exact firmware identity/stages, actual arbitrary-program argv/stdout/rc receipt, or immutable collector row |
| x86_64 | diagnostic PASS retained | blocked by compiler lineage, clean source, nonce, firmware contract |
| arm32 | concurrent diagnostic nonce + complete `/SYS/APPS` listing + hello/browser launch/render markers retained | not a matrix PASS: no admitted compiler/kernel provenance, clean-source identity, exact firmware artifact/stages, or immutable collector row; marker launch is not the required arbitrary-program argv/stdout/rc receipt |
| arm64 | real mounted PT_LOAD → EL0/SVC → exit-37 slice implemented; focused static contract PASS 10/10; earlier diagnostic still failed before this change | **not a matrix PASS**: admitted rebuild, ELF admission, and fresh nonce-correlated QEMU boot/list/stdout/exit/reap run required |
| riscv32 | concurrent diagnostic nonce + complete `/SYS/APPS` listing + hello/browser launch/render markers retained | not a matrix PASS: no admitted compiler/kernel provenance, clean-source identity, exact firmware artifact/stages, or immutable collector row; `-bios none` bypasses board firmware and marker launch is not arbitrary-program argv/stdout/rc evidence |
| riscv64 | nonce-bound ELF, exact mounted FAT-byte gate, user `ecall 60`, saved kernel return, exit `37`, and post-return reap are implemented; corrected focused simulator/static diagnostic exits `0` under the bootstrap seed | **not a matrix PASS**: confirm with the production toolchain, then run fresh QEMU with compiler/kernel/source/OpenSBI provenance and target stdout/exit/reap receipt |

### Real filesystem execution implementation gate (2026-08-12)

This gate is newer than the retained diagnostic serials and does not promote them.

| Guest | Implementation/static evidence | Live evidence | Verdict |
|---|---|---|---|
| ARM64 | mounted real ELF slice; `arm64_user_exit_return_contract_spec.spl` **PASS 10/10** | no post-change QEMU run | PARTIAL, live pending |
| RV64 | canonical VFS, mounted-byte nonce admission, supervisor return, exact-child reap, and target markers restored; source/static and C syntax pass | none | PARTIAL, production/live pending |
| x86_32 | real i386 ELF32 payload/static gate PASS; focused ownership spec hit the 120-second daemon-worker timeout before examples executed | none; current DPL3 `int 0x80` gate is invoked from ring 0 and has no user-entry/return/reap owner | PARTIAL, live blocked/spec timeout |
| ARM32 | authenticated transition, mounted staging, User/SVC return, parent-authoritative cleanup/reap and canonical entry are implemented; static/ARM syntax gates pass | none | PARTIAL, production/live pending |
| RV32 | pure nonce-bound ELF32 builder/simulator and mounted-byte gate diagnostic PASS 4/4; gate explicitly reports `rv32-sv32-live-entry-not-installed` | none | PARTIAL, live blocked |

RV64 production confirmation command is `SIMPLE_LIB=src bin/simple test test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl --mode=interpreter`; the completed bootstrap-seed diagnostic must not be promoted as production evidence. ARM64 and RV64 must each use the canonical bounded matrix wrapper in a fresh session. No static result, prior marker transcript, or positive PID satisfies live execution.

x86_32 static evidence is `scripts/check/check-simpleos-x86-32-user-elf.shs` PASS plus `mounted_elf32.S`; it does not supersede the timed-out ownership spec or prove CPL3. RV32 static/simulator evidence remains PASS 4/4, but its exact mounted-byte admission intentionally returns `-95` (`rv32-sv32-live-entry-not-installed`). Both rows remain blocked until their architecture-owned user-entry, trap-return, status, and reap paths exist and produce fresh live receipts.

### Fresh four-row Linux diagnostic receipts (2026-08-12)

These receipts improve diagnostic confidence only. They were produced outside
the closed-schema 24-cell collector and therefore do not change `PASS 0 /
BLOCKED 24`.

| Guest | Exact retained evidence | Observed diagnostic markers | Retained SHA-256 |
|---|---|---|---|
| x86_32 | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/x86-32-ls-20260812T035500Z/serial.log`; sibling `x86_32.img` and `hashes.txt` | `SIMPLEOS_QEMU_NONCE=nonce-x86_32-20260812T035500Z`; `FS_LS_BEGIN path=/SYS/APPS`; ten generic entries from `HELLOSMF.SMF` through `STEAM204.SMF`; `FS_LS_END status=pass`; initrd, hello, browser, payload, app-execution markers; `TEST PASSED` | image `33f1bfafaaff64aaa4dac7f20a392f2c6246c13c0131db53ad9f290ea48b559c`; serial `9f69d8a5edce7c52bb1b92a0f0409a3cd0a35e8ec2713d7cfcf51f12efb6473d` |
| arm32 | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/nonce-ls-three-20260812T034000Z/arm32.serial`; sibling `arm32.img` and `hashes.txt` | nonce `nonce-arm32-20260812T034000Z`; complete ten-entry `/SYS/APPS` listing; `ELF_LOAD_OK`; `SMF_CLI_LAUNCH_OK`; browser `SMF_WM_GUI_LAUNCH_OK`; `NATIVE_GUI_PROCESS_RENDER_OK`; `TEST PASSED` | image `51101e0de1a33e202b5167b421b38dd879a3e6800689ee9441a31e4699171fc7`; serial `3ac28fd7e5c64fd62be9a81556283ae7831b5ff428d2690ba187b73449abf374` |
| riscv32 | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/nonce-ls-three-20260812T034000Z/riscv32.serial`; sibling `riscv32.img` and `hashes.txt` | nonce `nonce-riscv32-20260812T034000Z`; complete ten-entry `/SYS/APPS` listing; `ELF_LOAD_OK`; `SMF_CLI_LAUNCH_OK`; `SMF_WM_GUI_LAUNCH_OK`; `NATIVE_GUI_PROCESS_RENDER_OK`; `TEST PASSED` | image `f28c1d54d7a1df3447dce08d4b4895a3be693e08e88f33259b48135ee487777a`; serial `97cca348d698da6606bba6947428832cef7b4176fb3c608e75a4c385f69d2305` |
| riscv64 | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/nonce-ls-three-20260812T034000Z/riscv64.serial`; sibling `riscv64.img` and `hashes.txt` | nonce `nonce-riscv64-20260812T034000Z`; complete ten-entry `/SYS/APPS` listing; `SMF_DISCOVERY_OK`; `ELF_LOAD_OK`; `SMF_CLI_LAUNCH_OK`; `SMF_WM_GUI_LAUNCH_OK`; `NATIVE_GUI_PROCESS_RENDER_OK`; `SIMPLEOS_RISCV_SMF_FS_PASS`; `TEST PASSED` | image `0b38df8b1b6e09dec73ca17918aae6cff7287ba0f69e12132a677a734015ffe9`; serial `f637e3850eb99928b9359540dadfe473144c70bfd9c089946fc94320f3fd1e7e` |

The concurrent ARM/RISC-V receipt directory proves those three serials and
images were retained together, but `hashes.txt` does not include kernel or
compiler hashes, source commit/tree identity, firmware identity, host
admission, or collector schema fields. The x86_32 receipt likewise proves the
new real dirent listing, not the remaining lineage/firmware/arbitrary-program
requirements. None may be relabeled as PASS by copying these hashes into a
matrix row.

The observed x86_32 `app execution ok`, ARM/RISC-V `SMF_CLI_LAUNCH_OK`, GUI
launch/render, and final PASS strings are reclassified as package/load-state
diagnostics. Source audit proves that the retained payload instructions were
not entered and no target-origin stdout or exit status was captured. See
`doc/08_tracking/bug/sosix_synthetic_filesystem_program_execution_2026-08-12.md`.

### Exact REQ-SQ-005 firmware gaps

The six descriptors now expose explicit firmware identity and boot mode, and
the immutable collector rejects either field when absent. This is contract
hardening only; no QEMU row was rerun and no diagnostic result is promoted.

| Guest | Descriptor identity / mode | Remaining board-representative gap |
|---|---|---|
| x86_32 | `implicit:qemu-platform-default` / `qemu-direct-kernel-initrd` | No named, hashed BIOS/UEFI image or firmware-stage transcript; direct `-kernel`/`-initrd` is not board firmware proof. |
| x86_64 | `implicit:qemu-platform-default` / `qemu-direct-kernel` | No named, hashed SeaBIOS/OVMF/Limine path or firmware-stage transcript; direct `-kernel` bypasses the claimed board boot chain. |
| arm32 | `none:qemu-loader-device` / `direct-loader-no-firmware` | QEMU loader-device injection has no U-Boot/UEFI firmware identity or firmware-stage transcript. |
| arm64 | `none:qemu-kernel-loader` / `direct-kernel-no-firmware` | QEMU `-kernel` has no AAVMF/UEFI or U-Boot identity and no firmware-stage transcript. |
| riscv32 | `none:-bios-none` / `direct-kernel-no-firmware` | `-bios none` explicitly bypasses OpenSBI/U-Boot; no board firmware artifact or stage transcript exists. |
| riscv64 | `qemu-bundled-opensbi:default` / `opensbi-default-with-kernel` | Firmware is selected but not resolved to an exact path/version/hash, and the retained transcript is not correlated to a named OpenSBI stage/build. |

Sabotage coverage in `check-collect-sosix-qemu-evidence.shs` deletes each new
field independently and requires collector rejection. Fresh evidence must
replace the diagnostic identities above with exact artifact provenance before
REQ-SQ-005 can pass.

### Reusable firmware admission seam (2026-08-11)

`src/os/qemu_systest_contract.spl` now provides a pure, fail-closed admission
helper for an exact absolute local firmware path, exact version, exact 64-byte
hex SHA-256 string, and nonempty ordered firmware boot-stage markers. Sabotage
coverage independently substitutes the path, version, hash, marker order,
missing markers, duplicate markers, relative paths, and malformed hashes.

The helper consumes facts observed by a future descriptor preflight; it does
not download firmware, derive authenticity, or launch QEMU. Descriptor
preflight is deliberately not wired yet: the six current descriptors do not
contain resolved exact local firmware path/version/hash tuples, and five still
describe implicit-default or no-firmware/direct-loader modes. Wiring those
rows would either encode invented provenance or unconditionally block every
existing diagnostic runner. Each guest must first pin its authoritative local
artifact tuple and board-specific ordered boot-stage markers. Until then,
REQ-SQ-005 remains not proven and no retained diagnostic row is promoted.

## REQ-SQ-008 compiler-in-filesystem audit and resume plan

### Media-profile authority correction (2026-08-12)

The rebuild descriptor now carries `compiler_in_filesystem` into
`make_os_disk.shs` for every row. The current ARM64 row is `false`, so its
filesystem image no longer requires or auto-discovers
`bin/release/aarch64-unknown-simpleos/simple`. A future `true` row is
fail-closed: it must supply `SIMPLEOS_SIMPLE_BINARY` explicitly, and the disk
builder validates the target ELF (plus the provenance stamp for x86_64).
Compiler-free rows may omit the payload; an explicitly supplied payload is
still target-validated. Disk-free self-tests sabotage both the false/omitted
and true/omitted cases. This correction is static evidence only; it did not
rebuild media or run QEMU, and it does not promote any matrix row to PASS.

No current collected matrix row was designated compiler-in-filesystem before
this audit: the row schema had no such field. Therefore none of the existing
24 cells can claim REQ-SQ-008, even if an unrelated image happens to contain a
file named `simple`.

The current build tree contains one candidate release staging tree for
`x86_64`: `build/os/release/simpleos-1.0.0-x86_64.img.contents/rootfs/` has a
2,300,776-byte statically linked x86-64 ELF copied to the canonical `/bin`,
`/usr/bin`, and `/sys/apps/simple{,_compiler,_interpreter,_loader}` paths, plus
`/SYS/SIMPLETOOL.SDN`. This is media-construction evidence only. It has no
correlated in-guest `--version`, compile, or output transcript and must remain
non-PASS. No corresponding current release payload was found for x86_32,
arm32, arm64, riscv32, or riscv64.

Resume in this order, without promoting host-side inspection:

1. For each guest descriptor, choose the exact install image and set
   `compiler_in_filesystem = true` only after its media build consumes a
   target-matching `src/app/simpleos_tool/main.spl` entry-closure binary with a
   qualified build stamp. Leave rows without that payload explicitly false.
2. Extend the guest command protocol to invoke the mounted
   `/usr/bin/simple --version`, create a nonce-bound `/tmp/hello.spl`, compile
   it to a guest-filesystem output, then execute that output. Record exact argv,
   exit codes, stdout, payload hash, image hash, host/guest/run identity, and
   nonce in two immutable artifacts referenced by the row fields.
3. Reject host `bin/simple`, seed/compiler-host binaries, fixed serial/SSH
   responses, marker apps, host-side compilation, missing canonical aliases,
   target mismatch, or artifacts not correlated to the row receipt.
4. Run the existing shared host wrapper for only the selected host and guest;
   do not add a second QEMU launcher. Import the authentic artifacts, then run
   the 24-cell collector. Windows, macOS, and FreeBSD cells remain non-PASS
   until executed on their actual hosts.

## Host audit

- Linux: diagnostic guest evidence exists; no release-complete six-row set.
- Windows: native parallel runner exists; it has not executed on Windows.
- macOS: explicitly postponed with six retained non-PASS bundles.
- FreeBSD: offline checksum-pinned media admission exists; base image is absent.

Windows wrapper status is therefore **implemented, native execution BLOCKED**;
its resume command is
`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-sosix-qemu-matrix.ps1 -AllGuests -Run -Parallel`.
FreeBSD requires the checksum-pinned
`/mnt/data/.simple/qemu/images/freebsd/FreeBSD-14.4-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2`
before the bootstrap smoke and actual-host six-row command can run. macOS stays
postponed by policy until an actual macOS operator owns the six-row execution.

Static audit on 2026-08-12 found all 18 retained external-host blockers present:
six each for Windows, macOS, and FreeBSD. Every row is `status=blocked` and uses
the host-specific operator (`windows-host-operator`, `macos-host-operator`, or
`freebsd-host-operator`) with reviewer `sosix-qemu-matrix-reviewer`. Their
artifacts remain valid immutable absence evidence. They do not prove readiness
or execution and retain the older serial resume string.

The native matrix wrappers currently write host `matrix.env` reports and row
logs, but neither wrapper writes the collector's closed per-row `evidence.env`
bundle (source/tree lineage, firmware identity/stages, image/program/transcript
hashes, nonce, owner/reviewer, and declared artifacts). Therefore the parallel
commands above are the exact next execution step, not by themselves a row
promotion. After native execution, the external-host evidence owner must retain
those fields in a new bundle producer or shared wrapper stage before the
24-cell collector can import a PASS. No existing blocked bundle may be edited
into a PASS.

## Next admissible gates

1. Restore at least the repository-required btrfs device-unallocated reserve
   (currently 1 MiB versus the ~5 GiB admission threshold) without deleting
   unrelated work; rerun the storage preflight before any bootstrap/QEMU job.
2. Reconfirm a stable tracked Rust input fingerprint, then deploy and identify
   a pure-Simple compiler once with seed fallback forbidden. Runtime C syntax
   is now green and the prior caches are hot.
3. Complete the registered-buffer VFS client/service backend path and run its
   focused specifications once.
4. In a fresh bounded session, rebuild and rerun only ARM64.
5. Run the six-row wrappers on actual Windows and FreeBSD hosts; retain macOS
   postponement until an actual macOS owner is available. Use `-Parallel` on
   Windows and `--parallel` on the Unix hosts so all six isolated rows execute
   under the frozen bounded parallel schedule.
6. Replace the corresponding blocked rows in the existing 24-cell immutable
   collector input and import a new content-addressed manifest.
