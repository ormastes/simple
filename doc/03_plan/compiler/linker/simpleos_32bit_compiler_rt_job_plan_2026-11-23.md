# Bounded ELF32 compiler-rt preparation job

Status: two failed GitHub campaigns are retained. The first configuration repair
passed all three real target configurations; the second exposed an oracle
spelling defect. Its minimal repair awaits Astra review before another attempt.

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
| arm32 | arm-none-eabi | `-march=armv7-a -marm -mfloat-abi=soft` |
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

## First real campaign and configuration repair

Run `45172244479`, job `137684442283`, exact source
`562313db4fc0ca393e7e4c6472c32527d3925371`, failed after successful checkouts,
VM utility installation and authenticated LLVM 23.1.1 provisioning. Artifact
`14818570814` (`simpleos-elf32-builtins-prep-45172244479`, 67589 bytes) and the
full job log are retained under
`build/verify/elf32-builtins-attempt-45172244479/`.

All three targets reached the same first failure in the exact pinned
`CompilerRTUtils.cmake:385`: `COMPILER_RT_DEFAULT_TARGET_TRIPLE` is forbidden
when `COMPILER_RT_DEFAULT_TARGET_ONLY=ON`. These are three failed rows with
one shared demonstrated cause, not three independent architecture failures.
All failed CMake caches, commands, stdout, stderr and resource observations are
preserved. No builtins build command, raw archive, or export validation occurred.
The ZLIB/zstd discovery notices are not the fatal boundary.

The repair removes only the explicit `COMPILER_RT_DEFAULT_TARGET_TRIPLE`
argument. Target-only selection remains enabled. The pinned macro derives its
triple from the already explicit `CMAKE_C_COMPILER_TARGET`; C/CXX/ASM target
bindings and generated-command target/ISA/ABI validation remain mandatory.
The next real attempt needs fresh configure outputs and command verification
for all three targets before building. No unchanged job rerun is authorized.
The repair history includes two prior source-review corrections and this first
real failed job; the six-cycle guard still applies to the same campaign.

The exact pinned target-selection chain also exposes an ARM32 spelling gap:
`armv7a-none-eabi` normalizes to architecture `armv7a`, while the pinned builtins
supported table omits that name. An isolated execution of the real pinned
`add_default_target_arch` and `filter_available_targets` functions reproduces the
empty selection. i686 and RV32 select their exact expected architectures.

The ARM builtins row therefore uses compiler target `arm-none-eabi` with explicit
`-march=armv7-a -marm -mfloat-abi=soft`; the selected architecture is `arm`. This
does not patch LLVM tables or disable target-only selection. The old and repaired
profiles produce an identical complete predefined macro set under the retained
local Clang 23.1.5 probe, with no objects built. That is scoped local evidence,
not equivalence of target spellings alone or proof for the VM's 23.1.1 compiler.
The next VM attempt must retain the actual target, ISA/ABI command flags, ELF
attributes, and derived archive evidence. The isolated source/selection receipts
are in `build/verify/elf32-builtins-attempt-45172244479/`.

## Second real campaign: assembler command spelling

Run `45183442000`, job `137722849031`, exact source
`0795989c076ccf89c1e78c240c2666f5c005ca66`, retained artifact `14823451200`
(`simpleos-elf32-builtins-prep-45183442000`, 89814 bytes). Inputs, logs, caches
and generated compiler commands are preserved under
`build/verify/elf32-builtins-attempt-45183442000/`; prior evidence is untouched.

The real 23.1.1 configurations now succeed for all targets and select exactly
`i386`, `arm`, and `riscv32`. Generated command inventories contain 140, 176 and
158 entries respectively. They stop at one shared oracle defect before Ninja
builds: CMake emits assembler commands as `-target <exact-triple>`, while the
oracle's equality check only accepted the C-driver spelling
`--target=<exact-triple>`. The count check already recognized both forms.
First rejected entries are i686 index 112 (`ashldi3.S`), ARM index 1
(`bswapdi2.S`), and RV32 index 0 (`mulsi3.S`); their actual target and ISA/ABI
arguments are correct. No archive or export gate was reached.

The repair accepts these two observed canonical spellings with exactly the same
target value and still requires one target occurrence. Duplicate/conflicting
target and ISA/ABI checks remain enforced. The complete 474 retained real
commands are checked offline with the repaired oracle before another build;
that source-oracle result is not a compiler build or guest qualification.
Two real jobs and the earlier source corrections remain in the same six-cycle
budget; no unchanged job or previously green C-provider campaign is rerun.
