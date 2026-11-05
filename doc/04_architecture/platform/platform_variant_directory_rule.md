# Platform Variant Directory Rule (OS -> ABI -> arch)

Status: ACCEPTED 2026-11-05. Scope: physical placement of platform-specific
source under a module's `platform/` (or SOSIX provider) root.

Relation to existing docs (most recent wins):
- `doc/05_design/compiler/simd_gpu_sosix_variation_final_2026-10-10.md` stays
  authoritative for **resolution machinery**: the resolver-only `variants/` root,
  `config/var.sdn` profiles, `@cfg` guards, "no competing target-directory
  resolver", and "move an owner, never copy it". This rule adds nothing to that
  machinery; it only fixes **directory names and nesting** inside the
  layer-owned implementation directories that doc leaves in place.
- Where that doc says "optional subdirectories by ISA/ABI only when moving the
  actual owner", this rule supplies the naming those subdirectories must use.
  Empty skeleton directories carrying only a `FILE.md` manifest are allowed (they
  hold no code, so they are not copies).

## 1. Canonical hierarchy

```text
<module>/platform/                    # level 0: all-platform common code
  <os>/                               # level 1: OS-common code
    <arch>/                           #   single-ABI OS: ABI implied
    <abi>/                            #   multi-ABI OS only
      <arch>/                         # level 3: OS+ABI+arch specific
```

`common` is the **logical** name of each level's shared code. It is the parent
directory itself, never a literal `common/` subdirectory: files directly in
`platform/` are all-platform common, files directly in `platform/windows/` are
Windows-common, and so on. This keeps existing flat `platform/` files valid at
level 0.

### Canonical names (aligned with target triples)

| Axis | Canonical | Triple component | Forbidden aliases |
|---|---|---|---|
| os | `linux` | `*-linux-*` | — |
| os | `freebsd` | `*-freebsd` | — |
| os | `macos` | `*-apple-darwin` | `mac`, `darwin`, `osx` |
| os | `windows` | `*-windows-*` | `win`, `win32`, `win64` |
| os | `simpleos` | `*-simpleos` / `*-none` kernel | `sos` |
| abi (windows) | `mingw` | `windows-gnu`, `windows-gnullvm` | `gnu`, `gnullvm` |
| abi (windows) | `msvc` | `windows-msvc` | `clang-cl` |
| arch 32 | `x86` | `i686` | `i386`, `i686`, `ia32` |
| arch 64 | `x86_64` | `x86_64` | `amd64`, `x64` |
| arch 32 | `arm` | `armv7`/`thumbv7` | `armv7`, `arm32` |
| arch 64 | `aarch64` | `aarch64` | `arm64` |
| arch 32 | `riscv32` | `riscv32gc`/`riscv32imac` | `rv32` |
| arch 64 | `riscv64` | `riscv64gc` | `rv64` |

Decisions:
- **`aarch64`, not `arm64`.** Directories today say `arm64` (6 dirs) but every
  target triple and 118 compiler files say `aarch64`; the resolver keys on the
  triple, so the directory follows the triple. Existing `arm64` dirs are frozen
  legacy (see §4).
- **`mingw`, not `gnu`, for Windows.** The triple says `windows-gnu`, but `gnu`
  on Linux means glibc; `mingw` names the Windows lane unambiguously and matches
  the toolchain policy (llvm-mingw UCRT is the default lane, `msvc` is the
  optional `--msvc` lane). The resolver maps `windows-gnu`/`windows-gnullvm` to
  `mingw`.
- Only **Windows** is multi-ABI. Linux is `gnu` implied (a future `musl` lane
  would make Linux multi-ABI: `linux/gnu/<arch>`, `linux/musl/<arch>`; until
  then `linux/<arch>` is canonical).

### Supported matrix (the skeleton the check requires)

| os | abi level | arch dirs |
|---|---|---|
| linux | implied gnu | x86, x86_64, arm, aarch64, riscv32, riscv64 |
| freebsd | implied | x86_64, aarch64, riscv64 |
| macos | implied | x86_64, aarch64 |
| windows | mingw, msvc | x86, x86_64, aarch64 (under each abi) |
| simpleos | implied | x86_64, aarch64, riscv32, riscv64 |

ARM32/x86-32/RV32 directory slots exist so placement is decided before code
lands; target registration and validator parity for them remain the separate
work item named in the 2026-10-10 design §1.1.

### Fallback order (most specific -> common)

```text
windows/mingw/x86_64 -> windows/mingw -> windows -> platform
linux/riscv64        -> linux         -> platform
```

Never across a sibling: no `riscv64 -> riscv32`, `x86_64 -> x86`,
`aarch64 -> arm`, and no `mingw -> msvc`. A 64-bit target with no 64-bit
variant falls back to the OS-common level, never to the 32-bit variant.

## 2. Resolution

- HIR stays target-neutral (all variants visible to analysis). MIR lowering /
  the build driver selects the variant from the canonical target triple
  (`80.driver/canonical_target_registry_owner_v1.spl`), through the existing
  `@cfg` guards and the `variants/` resolver — no new resolver.
- Triple -> path: `os = map(triple.os)`, `abi = map(triple.env)` (windows only),
  `arch = map(triple.arch)` per the table, then walk the fallback chain.
- **May differ** between variants: bodies, private helpers, extern *bodies*.
- **Must not differ**: the public API surface (same public `fn` names and
  signatures as siblings / the common contract) and `extern fn` signatures across
  ABI variants (`mingw` and `msvc` declare byte-identical externs).

## 3. Rules

1. **No ad-hoc platform conditionals in common code** when a variant dir exists:
   `if os == "windows"`, `@cfg(os=...)` in level-0 files, or `#ifdef _WIN32` in
   a level-0 C file are violations once a matching `<os>/` variant exists. Move
   the branch into the variant.
2. **Full API per variant.** Each variant implements every public name of its
   common contract or stubs it explicitly with a `TODO` comment plus a failing
   `assert` (fail-fast, never a silent no-op).
3. **C runtime follows the same split.** `_MSC_VER` vs `__MINGW32__` code goes
   under `windows/msvc/` vs `windows/mingw/`; `_M_ARM64`/`__aarch64__` code goes
   under the `aarch64/` dir; `platform_<os>.h` belongs in `<os>/`.
4. **Names only from §1 tables**, in hierarchy order (os, then abi, then arch).
   `arch/<arch>` style containers (e.g. `src/os/kernel/arch/`) are allowed for
   kernel/HAL code that has no OS axis.

## 3a. Compiler: canonical MIR + per-ABI lowering

**Levels.**
- **HIR**: immutable and target-neutral; records symbolic target dependencies only.
- **Canonical MIR**: control flow, ownership, memory ops and *logical* calls (logical
  params only). Shared by `windows-gnu` (llvm-mingw) and `windows-msvc` (clang-cl),
  and by every arch.
- **ABI-lowered MIR**: per target ABI. It holds physical argument placement, external
  layout, symbol mangling, calling convention, the EH boundary and ABI thunks.

**MinGW vs MSVC.** These differ: C++ layout and mangling (Itanium vs Microsoft), the
EH ABI, the CRT, debug info (DWARF vs CodeView/PDB) and the linker (`lld` vs
`lld-link`). These are shared: plain C interfaces, Simple-owned classes, generics,
async and memory. Both use the COFF object format.

**ABI overlays.** An overlay on canonical MIR carries only what changed: ABI
descriptors, symbol refs and lowered instructions. Don't duplicate a function's MIR
when its lowering is identical. Once control flow or instructions differ, emit a
separate immutable target artifact. An overlay never hides a real code difference.

**Cache keys.**

| Artifact | Key |
|---|---|
| HIR | source + semantic deps |
| Canonical MIR | HIR + lowering version |
| ABI MIR | canonical MIR hash + target triple + ABI spec + target features + lowering version |
| OBJ | ABI MIR + LLVM version + opt/codegen settings + runtime/object-format options |

**Identity.** The driver name (`clang` vs `clang-cl`) never decides MIR or cache
identity. Only the triple and the ABI spec do (`x86_64-w64-windows-gnu` vs
`x86_64-pc-windows-msvc`).

**Bound on the directory rule.** OS/ABI/arch *source* dirs (SOSIX, runtime C) exist
only for the OS and runtime surface, such as CRT and syscall differences. Simple
compiler code and Simple-owned libraries never fork per ABI. ABI differences live in
the compiler's ABI-lowering stage. In practice, `windows/mingw/` and `windows/msvc/`
dirs are expected only in C runtime and SOSIX CRT-facing providers.

### Symbol mangling

| Symbol class | linux / freebsd (ELF) | macos (Mach-O) | windows mingw | windows msvc |
|---|---|---|---|---|
| Simple to Simple | one stable Simple scheme | same | same | same |
| C extern, 64-bit | `name` | `_name` | `name` | `name` |
| C extern, x86 32-bit | `name` | n/a | `_name`, `_name@N` (stdcall), `@name@N` (fastcall) | same as mingw |
| C++ extern | Itanium | Itanium | Itanium | Microsoft |

Rules:
- Simple's own mangling is **one** scheme on every target. A Simple-to-Simple call
  never varies by ABI.
- Foreign-symbol decoration (the leading underscore, `@N`, Itanium vs Microsoft) is
  applied **only** in ABI lowering, from the target descriptor plus the extern
  declaration's attributes. It never appears in canonical MIR or in source dir
  names.
- The seed mangler (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`)
  and the pure-Simple mangler must produce identical names. PR #6869 (seed-mangler
  facade-crossing fix) is the reference case for drift.

### Parameter passing

| ABI (targets) | Int / FP arg regs | Aggregates | sret | Notes |
|---|---|---|---|---|
| Win64 (windows mingw + msvc, x86_64) | rcx, rdx, r8, r9 / xmm0-3, **positional** | 1/2/4/8 bytes by value in a register; everything else by hidden pointer | rcx | 32-byte shadow space; same for mingw and msvc |
| SysV x86_64 (linux, freebsd, macos) | rdi, rsi, rdx, rcx, r8, r9 / xmm0-7 | ≤16 bytes classified INTEGER/SSE into registers, otherwise memory | rdi | `al` = number of vector regs for varargs |
| AAPCS64 (aarch64 linux / macos / windows) | x0-x7 / v0-v7 | HFA/HVA up to 4 members in v regs; ≤16 bytes in x regs; otherwise by reference | x8 | Apple: variadic args always on the stack. Windows arm64: variadic FP args go in x regs; no red zone |
| RISC-V lp64d (riscv64) / ilp32d (riscv32) | a0-a7 / fa0-fa7 | ≤2×XLEN in registers (int+fp pairs flattened), otherwise by reference | a0 | varargs use int regs only, with an aligned register pair for 2×XLEN |
| x86 32-bit (linux, windows) | cdecl: stack. stdcall: callee pops. fastcall: ecx, edx | memory | hidden first stack arg | stack alignment 4 bytes (win32) vs 16 bytes (linux i686 SysV) |
| AAPCS32 (arm) | r0-r3; hard-float adds s0-s15/d0-d7 (`gnueabihf`); soft-float uses int regs (`gnueabi`) | ≤4 bytes in r0, otherwise memory | r0 | 8-byte alignment for 64-bit args |

Common across all of them: varargs follow the per-ABI rule above.
`bool`/`i8`/`i16` are extended by the caller to 32 bits (sign or zero per type).
Apple arm64 and RISC-V additionally require extension to XLEN or 32 bits as their
ABIs specify. Struct return follows the sret column.

Rules:
1. All of these decisions live in the ABI-lowering stage, driven by a **per-target
   ABI descriptor table** keyed by triple + ABI spec. Scattered `if os/arch`
   conditionals in MIR or codegen are not allowed.
2. Canonical MIR carries logical params only.
3. **Win64 by-value aggregates larger than 8 bytes, or not 1/2/4/8 bytes, go by hidden
   pointer, consistently at both caller and callee.** The Option-word and by-value
   struct-copy miscompiles (#6933 and the stage2 Option-word bugs) are exactly this
   class of bug.
4. Cross-check: a spec verifies every generated thunk and extern call site against
   the descriptor table for each supported triple.

## 4. Migration plan (no moves in the doc PR)

Current violations (survey 2026-11-05, release/1.0.0):
- `arm64` dirs (6): `src/runtime/startup/{baremetal,linux,macos,windows}/arm64`,
  `src/lib/nogc_async_mut_noalloc/baremetal/arm64`, `src/os/kernel/arch/arm64`.
- `variants/platform/mac` -> `macos`.
- `src/runtime/platform/` flat OS files at level 0: `platform_{linux,macos,
  freebsd,win}.h`, `async_{linux_epoll,linux_uring,macos,freebsd,windows}.c`,
  `runtime_win_*.h`, `windows_*.h`, `test_platform_win.h`, `test_arm64.h`,
  `test_x86_64.h`.
- C runtime ABI ifdefs inline in common files: `_WIN32` in 109 files,
  `_MSC_VER` 26, `__aarch64__` 23, `_M_ARM64` 7, `__MINGW32__` 1.


Compiler gaps (TODO, measured against §3a on release/1.0.0, 2026-11-05):
- TODO: `00.common/mir_target_context.spl` carries `abi` into MIR, and its ABI
  spellings are ad hoc (`macho`, `sysv`, and `gnu` for Windows). Canonical MIR should
  not branch on ABI. Move this to the ABI-lowering descriptor and canonicalise the
  spellings to the triple env.
- TODO: there is no per-target ABI descriptor table. Win64/SysV/AAPCS decisions are
  spread across `30.types/_TypeLayout/layout_core.spl` and
  `70.backend/backend/native/isel_x86_64.spl`. Create a single descriptor owner.
- TODO: there is no separate ABI-MIR artifact or cache key. The object key
  (`80.driver/driver_build/hir_variant_object_key_v1.spl:52`) folds
  arch-os-abi-backend, but no canonical-MIR-hash → ABI-MIR key exists. Add the
  §3a key ladder.
- TODO: confirm the driver name (`clang`/`clang-cl`) never enters a cache key.
  Today it is only implicit, via the producer-identity fingerprint.
- TODO: add a seed `mangle.rs` vs pure-Simple mangler parity spec (after #6869).
- TODO: add a Win64 >8-byte aggregate by-pointer caller/callee consistency spec
  (the #6933 class).
- TODO: add a thunk/extern-call descriptor cross-check spec for every supported
  triple.
- TODO: x86/arm/riscv32 descriptor entries (cdecl/stdcall/fastcall, AAPCS32
  hard/soft float, ilp32d) do not exist yet.

Order: (1) land skeleton + check (baseline freezes all of the above);
(2) rename `arm64 -> aarch64` and `mac -> macos` (pure renames, one PR each
root); (3) move `src/runtime/platform` OS headers/async files into `<os>/`;
(4) split `_MSC_VER`/`__MINGW32__` blocks into `windows/{msvc,mingw}`;
(5) Simple `platform/` modules last. Each step shrinks the baseline; the
baseline never grows.

## 5. Enforcement

`scripts/check/check-platform-variant-dirs.shs` (POSIX sh, `--selftest`
first and fatal). Checks: variant names in the allowed sets and hierarchy order;
sibling variants expose the same public `fn`/`extern fn` names (missing names
listed); `extern` signatures identical across ABI siblings; no new platform
conditionals in level-0 files; skeleton present for every §1 matrix cell under
each registered root. Baseline-relative: current violations frozen in
`scripts/check/platform_variant_dirs_baseline.txt`; new or grown ones FAIL.
Verdict line: `PASS — <n> ...` / `FAIL — ...` / `ERROR — nothing was checked`.
Wired as an advisory push-tier row (`config/check/must_check_gates.sdn`) and in
the extended CI job.
