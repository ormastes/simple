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
