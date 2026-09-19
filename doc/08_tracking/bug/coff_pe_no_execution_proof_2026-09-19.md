# COFF/PE capsule has no execution proof, and REL32_1..5 have no fixture

- **Filed:** 2026-09-19
- **Lane:** E1 (COFF/PE, plan lane A10 Windows slice)
- **Status:** open, blocked on host capability (not on code)

## 1. No execution proof for any PE image

`src/compiler/70.backend/linker/coff/coff_static_link.spl` produces a PE32+
EXE that is byte-identical to `lld-link 23.1.0 /timestamp:0` on the fixture
objects (`test/01_unit/compiler/backend/linker/pe_exec_writer_spec.spl`, 20/20).
Byte-identity with the reference linker is strong evidence, but it is **not**
an execution proof, and this record exists so nobody upgrades it to one.

This machine has no Windows host and no wine:

```
$ command -v wine wine64 wineconsole   # (nothing)
```

so no image produced by this lane has ever been run. The build host is aarch64
Linux; clang cross-compiles to `x86_64-windows-msvc` and `lld-link`
cross-links, but neither executes the result.

What would close it, in increasing order of fidelity:
1. `wine` on this host running the fixture EXE and reporting its exit status;
2. a Windows x86_64 CI runner;
3. per `.claude/rules/board-runnable.md`, a real Windows machine.

Until one exists, every claim about this capsule must stay structural. The
plan row (§13) and `test/fixtures/linker/coff/RECIPE.md` both say so.

Note that the fixtures are deliberately freestanding with `/nodefaultlib` and
make no imported call, because no MSVC headers or CRT are available here. Even
with wine, running them would prove only that the image loads and the entry
returns — not that an import-using program works, since the import table is
not implemented at all (named `UnsupportedFeature`).

## 2. IMAGE_REL_AMD64_REL32_1..REL32_5 have no end-to-end fixture

The value formulas are implemented and specified
(`coff_reloc_compute`, `coff_reloc_oracle_spec.spl`: `S + A - P - 4 - N`), but
**no object in the tree exercises them through a real link**, and none can be
produced from this toolchain.

Measured: LLVM's COFF assembler encodes `movl $imm, sym(%rip)`,
`movb $imm, sym(%rip)` and `movw $imm, sym(%rip)` as a plain
`IMAGE_REL_AMD64_REL32` with the instruction-length bias pre-folded into the
displacement field, rather than emitting `REL32_4` / `REL32_1` / `REL32_2`:

```
$ clang -c --target=x86_64-windows-msvc r.s -o r.obj
$ llvm-readobj --relocs r.obj
    0x2  IMAGE_REL_AMD64_REL32 counter
    0xC  IMAGE_REL_AMD64_REL32 flag
    0x14 IMAGE_REL_AMD64_REL32 halfw
```

MSVC's `ml64`/`cl` do emit them, so a fixture would need an object built by the
Microsoft toolchain (or a hand-assembled COFF object committed as bytes). The
formulas are therefore covered by spec-level unit tests only. This is recorded
rather than papered over: a reader must not assume the REL32_N rows have the
same evidence class as REL32, ADDR64, ADDR32NB, SECREL and SECTION, which are
all driven through a real link against the lld-link golden.

## 3. `$`-grouped section contributions are not ordered by full name

lld sorts the contributions inside one output section by their FULL input
section name, so `.text$mn` precedes `.text$zz`. This capsule keeps input order
within each of its two placement phases (file-backed, then zero-fill).

No fixture in the tree uses `$`-grouped sections — clang does not emit them for
these programs — so the two agree byte-for-byte on everything measured here.
They would differ in member ORDER (not in the section set, sizes or flags) on
an MSVC-produced object, which typically does use `.text$mn`. Closing it needs
either an MSVC-built fixture or a hand-assembled `$`-grouped object, plus a
sort key that still places zero-fill members last; recorded here so the gap is
not mistaken for parity that was measured.

## 4. ADDR32NB against an absolute symbol: we reject, lld wraps

`IMAGE_REL_AMD64_ADDR32NB` is `S - ImageBase`. For an absolute symbol `S` is a
small constant, so at the default base `0x140000000` the result is negative and
the oracle's unsigned-32 width check rejects it by name.

lld-link does not reject it: it lets the subtraction wrap and writes
`0xC0001234` for `absval = 0x1234`.

Rejecting is the safer reading — an image-relative field that is not inside the
image is almost always a mistake, and D4 says reject rather than mask. But it
IS a measured divergence from the oracle, it is pre-existing (it predates the
absolute-symbol work in this lane), and it is recorded here rather than left
implied. If a real corpus ever needs lld's behaviour, the change belongs in
`coff_reloc_compute` with a golden, not in a caller.

## 5. SECTION against an absolute symbol is implemented, SECREL is not

Resolved, and noted here because the first version of this lane got it wrong in
a way worth remembering: the D4 footer claimed lld "also refuses outright" for
the whole section-relative family. Measured, that is false for
`IMAGE_REL_AMD64_SECTION` — lld exits 0 and writes `numOutputSections + 1`
(`COFF/Chunks.cpp` `applySecIdx`, "required for compatibility with MSVC").
`coff_abs_section_index` now reproduces it, including the detail that the
synthesized `.reloc` COUNTS toward the total (`0x0003` for a 2-section image,
`0x0004` when a base relocation adds `.reloc`). Goldens: `secidx_x64.lld.exe`
and `secidx2_x64.lld.exe`. Only SECREL/SECREL7 remain Errs, matching lld.

## 6. The SizeOfHeaders reservation heuristic has a measured boundary

`coff_reserved_out_count` reproduces lld's "size the headers over the sections
created, before empty ones are removed, always including `.reloc`" rule, and it
is byte-exact on all seven goldens. It is a reverse-engineered heuristic, not a
spec rule, and `disc_x64.obj` is the one measured input where it disagrees:
lld reserves `0x400`, we reserve `0x200` (our name-based count gives
`{.text, .data} + .reloc` = 3 → 504 → 512).

Why lld reserves a fourth entry there is not established. The obvious theory —
that lld bins `.bss` separately from `.data` because their masked
Characteristics differ in the CNT bits — is contradicted by `chain_x64`, which
has the same `.data`/`.bss` shape and reserves only `0x200`. The distinguishing
input is the hand-set `IMAGE_SCN_MEM_DISCARDABLE` bit, and the mechanism has
not been traced to lld's source.

Scope: reachable only by hand-patching a section header. No compiler emits a
DISCARDABLE section carrying an ADDR64, and every compiler-produced fixture in
this tree is byte-exact. The consequence is a valid PE with a smaller header
than lld would write, not a malformed one — section contents, the section
table, and the (empty) base-relocation directory all match. `disc_x64`'s spec
therefore asserts the base-relocation and Characteristics behaviour it exists
to pin, and deliberately does NOT assert byte-identity, rather than pinning a
number that is not understood.
