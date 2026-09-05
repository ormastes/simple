# Lane B1 — clang self-compile WITNESS: host-side preparation

Status: HOST-SIDE PREPARATION COMPLETE (2026-08-06). No QEMU/OVMF was run this
round; the in-guest execution and comparison belong to the next round.
Companion tldr: `b1_clang_selfcompile_witness_tldr.md`.
Parent plan: `toolchain_selfhost_bootstrap_plan.md` § "Lane B1".

## 0. What B1 is, and what it is not

Goal G3 is "clang compiles clang on SimpleOS". A full self-build is structurally
out of reach today (FAT32 root-only/8.3 on the write side → no ~150k-file nested
LLVM tree; no `fork` on the ring-3 FS-exec path → no cmake/ninja/make and no
clang *driver*, only `clang -cc1`; guest runs 2–4 GB vs the many GB a self-build
needs). B1 is therefore the honest scoped witness:

> in-guest `clang -cc1` compiles ONE REAL LLVM/clang translation unit to an
> object, byte-compared against the host cross-build of the same input.

Preprocessing on the host to a single self-contained `.i` sidesteps both the
include-path problem and the nested-filesystem problem. Until Lane B4 passes,
every "clang bootstrap on SimpleOS" claim is scoped to exactly this.

## 1. TU selection — measured, not guessed

Every candidate below was actually preprocessed with the cross flags
(`--target=x86_64-unknown-simpleos`, sysroot + libc++ `isystem`, `-std=c++17`).
All of them need the sysroot's libc++ headers (LLVM's ADT/Support headers pull
`<cstdint>`, `<cstring>`, `<type_traits>`, `<limits>`, …), which is precisely why
preprocessing must happen on the host. `.i` sizes are with line markers
(`-E`, the naive form):

| TU (`llvm/lib/Support/`) | src lines | `.i` bytes | note |
|---|---:|---:|---|
| MathExtras.cpp | 31 | 387,644 | smallest, but only a couple of helpers — too close to a toy |
| **DivisionByConstantInfo.cpp** | **155** | **1,588,997** | **chosen** |
| ConvertUTF.cpp | 764 | 2,169,006 | real, but C-style; 2× the `.i` |
| LEB128.cpp | 43 | 2,810,964 | tiny body, huge `.i` |
| InstructionCost.cpp | 24 | 2,840,747 | |
| CRC.cpp | 107 | 2,861,620 | |
| ELFAttributes.cpp | 34 | 2,886,896 | |
| DJB.cpp | 83 | 2,897,329 | |
| StringSaver.cpp | 38 | 2,899,123 | |
| BlockFrequency.cpp | 64 | 2,913,781 | |
| SHA256.cpp | 286 | 2,945,255 | |
| BranchProbability.cpp | 113 | 2,985,539 | |
| Base64.cpp | 92 | 2,987,829 | |
| MD5.cpp | 298 | 3,034,097 | |
| StringExtras.cpp | 137 | 3,045,170 | |
| APFixedPoint.cpp | 621 | 3,110,115 | |
| ScopedPrinter.cpp | 49 | 3,415,510 | largest |

**Chosen: `llvm/lib/Support/DivisionByConstantInfo.cpp`.** Justification:

- It is genuinely LLVM code, not a toy: the Hacker's-Delight magic-number
  derivation (`SignedDivisionByConstantInfo::get`,
  `UnsignedDivisionByConstantInfo::get`) that LLVM's own DAG combiner uses to
  turn integer division by a constant into multiply+shift.
- It is built entirely on `APInt` — templated C++ with real inlining,
  `constexpr`, and non-trivial `-O3` codegen — so the object is a meaningful
  exercise of the compiler, not a memcpy wrapper.
- It has **no** I/O, no filesystem, no `errno`, no OS-facing calls, so nothing in
  the object depends on SimpleOS runtime behaviour.
- Its preprocessed form is the second-smallest measured and the smallest among
  the genuinely-substantial candidates.

**Actual staged size: `TU1.I` is 1,164,308 bytes (1.11 MiB)** — the shipped form
uses `-E -P` (line markers stripped), which is 27% smaller than the 1,588,997 in
the table and, more importantly, contains **zero host absolute paths**
(`grep -c /home/ormastes TU1.I` → 0). One 1.1 MiB file in the FAT32 root is well
within reach; nothing else has to be staged.

`-P` vs markers was verified to be codegen-neutral: the two objects differ in
exactly one thing — the `STT_FILE` symbol (`TU1.I` vs `DivisionByConstantInfo.cpp`)
and the resulting `.strtab` length. All code and relocations are identical.
Since the STT_FILE name is taken from the input file's **basename**, the guest
must read the file as `TU1.I` for a byte-exact result (see § 5).

## 2. Self-containment — proven, not asserted

Three independent checks:

1. `grep -c '^[[:space:]]*#[[:space:]]*include' TU1.I` → **0**. The only `#`
   lines left are 2,445 `#pragma clang` / `#pragma GCC` directives (libc++
   diagnostic pragmas), which need no header lookup.
2. Compiled through the driver with header search fully amputated **and a
   sysroot that does not exist**:
   `clang++ --target=x86_64-unknown-simpleos --sysroot=/nonexistent-sysroot
   -nostdinc -nostdinc++ -nobuiltininc -std=c++17 -fno-exceptions -fno-rtti -O3
   -DNDEBUG -fno-ident -x c++-cpp-output -c TU1.I` → exit 0.
3. That isolated object was **byte-identical** to the reference object built with
   the full flag set. So not only does it compile without headers, it compiles to
   the *same bytes* — the include environment provably contributes nothing.

`__DATE__`/`__TIME__` are a non-issue by construction: if present they are frozen
into the `.i` at preprocessing time on the host, so host and guest see the same
literal text. (This TU uses neither.)

## 3. Host reference object

Produced by `build/os/b1_witness/make_reference.shs`:

```
sha256(TU1.I) = e47b335dd4a8b343dec848ef590da07495d230a56d1e07c1c34584d484b5888b   1,164,308 B
sha256(TU1.O) = f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4      10,616 B
```

`readelf -h TU1.O` (excerpt): `Class ELF64`, `Data 2's complement, little endian`,
`OS/ABI UNIX - System V`, **`Type REL (Relocatable file)`**,
**`Machine Advanced Micro Devices X86-64`**, `Entry 0x0`, no program headers.
Exactly the expected ET_REL / EM_X86_64.

## 4. Reproducibility — the load-bearing result

A sibling lane observed that rebuilding the SimpleOS **Simple** payload twice
gives two different digests. That non-determinism does **not** extend to this
path. Measured here:

| experiment | result |
|---|---|
| Same `-cc1` line run twice, same cwd | **byte-identical** |
| 5 further full re-runs of `make_reference.shs` | all 6 digests identical |
| Run under `env -i` with different `HOME`, `TMPDIR`, `PATH` and a different output dir | **identical** |
| Run from a different cwd (simulating guest `/`) | **identical** |
| Input given as absolute path vs relative | **identical** |
| Different `-o` output filename | **identical** |
| `-main-file-name` set to a different value | **identical** (it does not reach the object; the `STT_FILE` symbol comes from the input basename) |

Conclusion: **clang `-cc1` on a preprocessed TU is deterministic**, so B1's
byte-comparison oracle is sound. The Simple-payload non-determinism is specific
to that build path and does not invalidate this lane.

Flags that make it reproducible (all are in the recipe and are **required**):

- `-fno-ident` — without it the object carries a `.comment` section holding the
  compiler's version banner. The host clang is `Ubuntu clang 20.1.8`; the
  in-guest `clang-20` is the fork's `20.0.0git`. That string alone would
  guarantee a byte difference. This is the single most important flag.
- `-fdebug-compilation-dir=/` and `-fcoverage-compilation-dir=/` — pinned so the
  compiler's working directory (host build dir vs guest `/`) cannot leak in.
  (With no `-g` these did not in fact change the bytes, but they are pinned
  because relying on that would be luck, not design.)
- No `-g` at all — debug info would embed paths and directory tables.
- `-main-file-name TU1.I` plus a guest input basename of `TU1.I` — the `STT_FILE`
  symbol is the input basename, so the guest file must be named `TU1.I`.
- `-frandom-seed` is **not** needed: this TU has no anonymous-namespace or
  internal-linkage entities whose mangled names would pick up the default seed,
  and the "different output filename" experiment above confirms no seed leakage.
  If a future B1 TU is chosen that does have them, add `-frandom-seed=TU1`.

### Flag availability in the GUEST binary — verified host-side

The flag set above was harvested from the **20.1.8 driver's** `-###` output, but
`-cc1` is an unstable internal interface and hard-errors on an unknown option. So
every flag was checked against the guest binary
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20` itself (no QEMU
needed) before the recipe was written:

- Method: `grep -acF -- "<option>" clang-20`. (An exact-line match against
  `strings` output is **fail-open here** — clang's OptTable stores option names
  in one concatenated string table, so `grep -xF` returns 0 for *every* flag,
  including ones that certainly exist. That false-negative was observed and
  discarded.)
- Controls, both run: positive `emit-obj` → 1 hit; negative `zzz-not-an-option`
  and `fno-really-not-an-option` → 0 hits each.
- Result: **all 21 checked options are present** in the guest binary —
  `emit-obj`, `disable-free`, `clear-ast-before-backend`, `disable-llvm-verifier`,
  `discard-value-names`, `main-file-name`, `mrelocation-model`, `mframe-pointer`,
  `fmath-errno`, `ffp-contract`, `mconstructor-aliases`, `funwind-tables`,
  `fdebug-compilation-dir`, `fcoverage-compilation-dir`, `fdeprecated-macro`,
  `ferror-limit`, `fgnuc-version`, `fskip-odr-check-in-gmf`, `faddrsig`,
  `fno-ident`, `c++-cpp-output`.
- (The same grep against `/usr/lib/llvm-20/bin/clang` returns 0 for everything —
  that host binary is a thin driver whose OptTable lives in
  `libclang-cpp.so`. It is not a usable control; the guest-side positive/negative
  controls above are.)

If a future flag turns out to be missing, drop it from **both** sides and
regenerate `TU1.O` — the reference must be built with the identical set.

### Residual risk R1 — compiler revision skew (declare it, do not hide it)

The host reference is produced by **Ubuntu clang 20.1.8**; the in-guest compiler
is built from the fork `github.com/ormastes/llvm-project@596122063`, which reports
**`20.0.0git`**. There is no host-runnable build of the fork (only
`build/os/llvm/host-tools/bin/{llvm,clang}-tblgen`), and rebuilding one is hours
of work explicitly out of scope. So a byte-exact result is *plausible* but not
*guaranteed*: any codegen change between 20.0.0git and the 20.1.8 release would
show up as a legitimate difference.

**R1 is narrower than it first looks — measured, not assumed.** The fork *does*
add SimpleOS as a first-class target (`Triple::SimpleOS` in
`llvm/lib/TargetParser/Triple.{h,cpp}`, `SimpleOSTargetInfo` in
`clang/lib/Basic/Targets/OSTargets.h`, a `SimpleOS` ToolChain in
`clang/lib/Driver/ToolChains/SimpleOS.cpp`, commits `6632b25a9`, `b0e410881`,
`3b33ba807`). But reading what those actually do:

- `SimpleOSTargetInfo` sets **only** preprocessor defines (`__simpleos__`,
  `__SIMPLEOS__`, `__unix__`, `__ELF__`, `_REENTRANT`) plus
  `WCharType=SignedInt` / `WIntType=UnsignedInt`. It changes **no** codegen
  default — no init-array/TLS-model/long-double/PIC override. So the guest's
  OS-aware `-triple` handling and the host's generic-ELF (UnknownOS) handling
  agree on everything that reaches the object, with `WIntType` the only
  theoretical exception (irrelevant to this TU, which never mentions `wint_t`).
- The `SimpleOS` **ToolChain** is a driver-level class and is bypassed entirely
  by `-cc1`.
- The predefines are moot: preprocessing happens on the host, whose clang parses
  `simpleos` as UnknownOS and therefore does *not* define `__unix__`/`__ELF__` —
  which is exactly why the cross build passes `-D__simpleos__=1` by hand. Both
  sides compile the identical `.i`, and that `.i` is preprocessed the same way
  the real cross build preprocesses every LLVM TU. Consistent by construction.

What remains of R1 is therefore plain upstream-revision skew between 20.0.0git
and the 20.1.8 release. Tier 1 is a reasonable expectation, not a long shot.

This is handled by a two-tier oracle rather than by weakening the criterion:

- **Tier 1 (the real accept):** byte-identical to `TU1.O`.
- **Tier 2 (explained divergence, only if tier 1 fails):** identical `.text`,
  `.rodata` and relocation content plus an identical symbol table, with any
  remaining diff attributed to the 20.0.0git↔20.1.8 revision skew and shown
  as a disassembly diff. A tier-2 pass must be *reported as tier 2*, never as
  "byte-exact".

Both tiers are implemented in `build/os/b1_witness/compare_object.shs`.
The clean way to retire R1 entirely is to build a host-native clang from the fork
and regenerate `TU1.O` with it; that is the recommended follow-up if tier 1 fails.

## 5. Staging + run recipe for the next round

**Stage (host → guest FAT32 root, 8.3 names, root directory only):**

| host artifact | guest path |
|---|---|
| `build/os/b1_witness/TU1.I` (1,164,308 B) | `/TU1.I` |
| — produced in-guest — | `/TU1.O` |

Only `TU1.I` is staged. The guest must see the basename **`TU1.I`** exactly
(uppercase 8.3), because the `STT_FILE` symbol is derived from it.

**Exact in-guest command line** (single `-cc1` invocation — no driver, no fork):

```
/CLANG20 -cc1 -triple x86_64-unknown-simpleos -emit-obj \
  -disable-free -clear-ast-before-backend -disable-llvm-verifier \
  -discard-value-names -main-file-name TU1.I \
  -mrelocation-model static -mframe-pointer=all \
  -fmath-errno -ffp-contract=on -fno-rounding-math -mconstructor-aliases \
  -funwind-tables=2 -target-cpu x86-64 -tune-cpu generic \
  -fdebug-compilation-dir=/ -fcoverage-compilation-dir=/ \
  -O3 -std=c++17 -fdeprecated-macro -ferror-limit 19 -fno-rtti \
  -fgnuc-version=4.2.1 -fskip-odr-check-in-gmf -vectorize-loops -vectorize-slp \
  -faddrsig -fno-ident -D__GCC_HAVE_DWARF2_CFI_ASM=1 \
  -o /TU1.O -x c++-cpp-output /TU1.I
```

Notes:
- Substitute the actual staged guest name of `build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20`
  for `/CLANG20` (8.3, e.g. `/CLANG20` or `/CLANG.ELF`).
- `-x c++-cpp-output` is mandatory: the `.I` extension is not a language clang
  infers, and it is what guarantees no header search is attempted.
- No `-resource-dir` is needed — a preprocessed TU never opens a builtin header.
- `-cc1` means the driver is bypassed entirely, which is what makes this runnable
  on the fork-less, `fork()`-less ring-3 FS-exec path.

**Comparison procedure:**

1. Retrieve `/TU1.O` to the host (`scripts/os/scp_retrieve_over_ssh_uefi.shs`).
   *Known hazard:* at the last L5 attempt this retrieval returned an **empty**
   object. A zero-length or truncated `TU1.O` is a **transport failure, not a
   compile failure** — check the size against 10,616 B before drawing any
   conclusion about the compiler.
2. `sh build/os/b1_witness/compare_object.shs <retrieved TU1.O>`.
3. Record the verdict verbatim: `TIER1 PASS`, or the tier-2 section-by-section
   table with the explanation.

**Evidence bar** (same as every other SimpleOS lane): OVMF-pflash real firmware,
never `-kernel`, never `isa-debug-exit`. Acceptance must rest on **positive
markers**, never on the absence of a failure line — the stub-fabrication channel
and the empty-`getfile` path both satisfy every absence condition. Required
transcript items:

1. the positive persist marker for the produced object — the L4 precedent is
   `[oo-nvme] persist /TU1.O -> OK`;
2. the retrieved object's **size = 10,616 B** and its sha256;
3. the `compare_object.shs` verdict line.

The `-cc1` exit status is recorded but is *not* the oracle on its own.

## 6. Artifacts (`build/os/b1_witness/`)

| file | size | sha256 |
|---|---:|---|
| `TU1.I` | 1,164,308 | `e47b335dd4a8b343dec848ef590da07495d230a56d1e07c1c34584d484b5888b` |
| `TU1.O` | 10,616 | `f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4` |
| `SHA256SUMS` | 402 | hashes of all five files |
| `make_reference.shs` | 1,904 | regenerates both, byte-reproducibly |
| `compare_object.shs` | 1,229 | tier-1/tier-2 comparison oracle |
| `check_guest_flags.shs` | 1,311 | guest `-cc1` option availability, with controls (`PASS — controls ok, 25 options present`) |

`make_reference.shs` honours `LLVM_SRC`, `CROSS_BUILD`, `SYSROOT`, `OUT`, `CXX`,
`CC1BIN` so it can be re-run on another machine or against a rebuilt fork.

## 7. What is explicitly NOT done here

- No QEMU/OVMF run of any kind (another lane owns the gates).
- No kernel, libc, or LLVM rebuild.
- Nothing committed or pushed.
- R1 (compiler revision skew) is open and declared, not mitigated.
