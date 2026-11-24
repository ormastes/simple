# Bounded ELF32 compiler-rt preparation job

Status: authored, awaiting Astra review; no GitHub build has started.

## Inputs and owner boundaries

The new workflow is `.github/workflows/simpleos-elf32-builtins-prep.yml`; the
finite build owner is `scripts/os/prepare-simpleos-elf32-builtins.shs`.
It reuses the existing `src/os/port/llvm/compiler_rt_cmake.cmake` initial-cache
fragment and official Linux installer
`scripts/setup/install-linux-phase23-llvm23.shs`. It invokes LLVM's standalone
`compiler-rt/lib/builtins` CMake project, not an LLVM/Clang build.

The existing `src/os/port/llvm/build.shs compiler-rt` cannot serve unchanged:
its architecture switch rejects i686/arm32, it requires a previously built
target Clang, and it unconditionally ensures a separate libc build. The new
helper does not change that owner or invoke its host-libc preparation.

- Exact Simple source: reviewed PR head or dispatched revision, checked out
  explicitly and compared to the expected 40-digit SHA before running commands.
- LLVM source: official 23.1.1 commit
  `6dfe1677ab8dffbc6ec13d53a1e0215d75147689`, verified through the GitHub API;
  sparse checkout includes only compiler-rt builtins/include/CMake and the
  common/LLVM CMake modules.
- Host tools: existing canonical official 23.1.1 Linux-X64 archive, exactly
  2014958380 bytes, SHA-256
  `832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c`.
  The installer verifies these before extraction. Actual selected compiler,
  archiver, nm, ranlib, readobj, CMake, and Ninja hashes are recorded separately.
- The earlier local C-provider campaign used Windows LLVM 23.1.5. Those results
  remain separate; this job makes no version-equivalence claim.
- Existing SimpleOS libc headers are input-hashed; the job does not build a
  complete sysroot or amend any SDK receipt.

## Finite VM graph

One Ubuntu 22.04 VM installs the shared official tools once. This runner is
selected because the canonical release requires ICU 70; installation explicitly
includes `libicu70`, CMake, Ninja, and xz utilities. Package installation occurs
only inside this disposable VM and its logs are retained.

The job timeout is 45 minutes. Each utility-install operation is bounded to ten
minutes; official tool provisioning is bounded to fifteen minutes. After
installation the helper requires at least 2 GiB free disk. Three target rows run
concurrently, each with one Ninja worker. Each row has a five-minute configure
and twenty-minute build deadline, a 3 GiB per-process virtual-memory limit,
1200-second per-process CPU limit, and 1 GiB per-file output limit. GNU time
records per-command elapsed time and maximum child RSS; these observations are
not an aggregate VM RSS measurement. Signal cleanup terminates and reaps each
owned command process group. Failed rows are retained while independent rows
finish; no automatic retry is scheduled.

| Row | Clang target | ISA/ABI |
|---|---|---|
| i686 | i686-unknown-none-elf | `-march=i686` |
| arm32 | armv7a-none-eabi | `-marm -mfloat-abi=soft` |
| riscv32 | riscv32-unknown-elf | `-march=rv32imac -mabi=ilp32 -mno-relax` |

All use freestanding static non-PIC compilation with the retained full flag
vectors. Atomic builtins are explicitly included because LLVM otherwise excludes
them by default; pthread locks are explicitly disabled so the actual standard
pointer-sized-atomic lock fallback is selected. This is preparation, not proof of
SimpleOS scheduler/interrupt compatibility or guest atomic correctness.

Seed variables are supplied before loading the initial cache, and all three
compiler target properties are explicitly bound afterwards. Every generated
compiler command must contain exactly the expected target and ISA/ABI flags;
duplicate, conflicting, or unrequested `-march`, `-mabi`, and `-mfloat-abi` flags
are rejected as well. Failure blocks compilation. Verbose Ninja output retains executed compiler
commands rather than treating CMake cache values alone as target proof.

## Artifact checks and quarantine

The helper requires one target builtins archive per row. It preserves the raw
archive, rejects duplicate or unsafe member names, extracts into an empty private
directory, and verifies every member's ELF32/little-endian machine identity.
It records member bytes/hashes, archive digest, source/input hashes, actual
commands, CMake cache and generated compiler commands, stderr, resources,
defined symbols, duplicate strong owners, and required compiler-ABI exports.
Unresolved atomic-helper ownership is rejected rather than hidden.
Required exports are checked on the derived archive's bytes after quarantine.
The symbol ownership check is not a recursion check; that unperformed check is
explicit in the derived receipt. ELF ABI flags and architecture attributes are
also retained for review without claiming full generated-Simple ABI qualification.

For ARM/RV32, the uniquely identified `__clear_cache` member is quarantined from
a separately derived archive; the raw bytes remain intact. The standard baremetal
implementation does not supply the required SimpleOS cache-sync contract. Derived
archive receipts explicitly say `missing-real-simpleos-owner`; no empty stub,
Linux syscall, or architecture-only assertion is substituted. i686 retains the
standard unified-cache implementation. Neither archive is installed into an SDK.

All receipts state `admission: none`. A green job proves only these archive
preparation checks. It proves no lint/test live closure, Simple linker execution,
kernel boot, phase completion, or guest result. Later SDK adoption must bind the
actual chosen archive/member inputs for both link engines and supply any real
cache-sync owner needed by surviving tool code.

## Trigger and next action

The workflow supports manual dispatch after registration. Before it exists on the
default branch, the one-time route is PR `labeled` with exact label
`simpleos-elf32-builtins-prep`, same repository, branch
`work/cross-compile-complete-20261123`, and base `release/1.0.0`. It does not run on
`synchronize`. Root must obtain Astra review before creating/applying that label
or dispatching. Contents/actions permissions are read-only, publication is absent,
and unadmitted diagnostics are retained even after failure. Root owns commit,
push, trigger, and subsequent exact source/run binding verification.
