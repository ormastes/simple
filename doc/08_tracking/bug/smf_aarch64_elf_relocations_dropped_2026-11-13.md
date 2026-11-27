# Every compiled `.smf` crashes on aarch64 Linux: ELF AArch64 relocations dropped (2026-11-13)

- **id:** `smf_aarch64_elf_relocations_dropped_2026-11-13`
- **severity:** P1 (every compiled SMF on aarch64 ELF hosts is unrunnable)
- **status:** fix-implemented-verification-pending (verified on aarch64 Linux; FreeBSD arm64 unrun)
- **file:** `src/compiler_rust/compiler/src/linker/object_parser.rs` (`map_relocation_type`)
- **reported by:** PR #8915 sibling lane, "Still open" section of
  `jit_module_namespace_member_access_unresolved_2026-11-13.md`

## Symptom

On the aarch64 DGX Spark host (Linux, ELF):

```
seed compile -o hi.smf hi.spl     # hi.spl = print("hi")   -> rc 0
seed hi.smf                       # Bus error (SIGBUS), core dumped
seed run hi.smf                   # same, rc 135
```

Reproduced with the release seed `seed-whileval` (release/1.0.0 head
`51ee52465f2`). Both runner spellings take the same path
(`simple_driver::exec_core::run_main` -> runtime `ModuleLoader`).

## Evidence

gdb at the fault:

- `pc = 0x3fda9bf7bfd`, `x0 = 0x910003fda9bf7bfd`, `x30 = <code base> + 0x20`.
- `x0` is the first 8 bytes of the module's own code
  (`a9bf7bfd stp x29,x30,[sp,#-16]!` / `910003fd mov x29,sp`).
- Caller is `run_main+312: blr x8` into the SMF code page.

Disassembly of the code section of `hi.smf`:

```
110: a9bf7bfd  stp  x29, x30, [sp, #-16]!
114: 910003fd  mov  x29, sp
118: 90000000  adrp x0, 0x0        <- never patched
11c: f9400000  ldr  x0, [x0]       <- never patched
124: 90000005  adrp x5, 0x0
128: f94000a5  ldr  x5, [x5]
12c: d63f00a0  blr  x5             <- jumps to the module's own instruction bytes
```

The GOT loads were never relocated, so `ldr` reads the code page base and
`blr` branches to instruction bytes used as an address.

## Root cause

`ParsedObject::parse` converts the Cranelift object into SMF relocations via
`map_relocation_type(kind, encoding, flags)`. The `object` crate (0.36.7)
classifies only a handful of ELF AArch64 relocations
(`ABS64/32/16`, `PREL64/32/16`, `CALL26 -> (PltRelative, AArch64Call)`);
everything else is `RelocationKind::Unknown` with `RelocationFlags::Elf`.
`map_relocation_type` only recovered the arm64 types from **Mach-O** flags, so
on ELF:

- `R_AARCH64_ADR_GOT_PAGE`, `R_AARCH64_LD64_GOT_LO12_NC`,
  `R_AARCH64_ADR_PREL_PG_HI21(_NC)`, `R_AARCH64_ADD_ABS_LO12_NC`,
  `R_AARCH64_LDST*_ABS_LO12_NC`, `R_AARCH64_JUMP26` fell through to
  `RelocationType::None` and were silently skipped by the loader;
- `R_AARCH64_CALL26` hit the generic `(PltRelative, _) => Plt32` arm, so the
  loader would write a raw x86-style i32 displacement over the `bl`
  instruction.

The SMF format and the runtime loader were already correct: the loader
implements `Arm64Branch26/Page21/PageOff12/GotLoadPage21/GotLoadPageOff12`
with a real GOT. Only the object -> SMF mapping was wrong.

## Classification

- Not a stale format version and not a loader/format bug.
- **aarch64-ELF-only by construction** (Linux/FreeBSD arm64). x86-64 ELF
  relocations (`PC32/PLT32/GOTPCREL/64`) are all classified by `object` and
  mapped; Mach-O arm64 was mapped through its flags. Not reproduced on x86 in
  this lane (no x86 host available here).

## Fix

`map_relocation_type` now takes the object's `Architecture`. For aarch64 ELF
it maps by `r_type` before any generic arm:

| ELF r_type | SMF type |
|---|---|
| `ABS64` | `Abs64` |
| `PREL32` | `Pc32` |
| `CALL26`, `JUMP26` | `Arm64Branch26` |
| `ADR_PREL_PG_HI21(_NC)` | `Arm64Page21` |
| `ADD_ABS_LO12_NC`, `LDST{8,16,32,64}_ABS_LO12_NC` | `Arm64PageOff12` |
| `ADR_GOT_PAGE` | `Arm64GotLoadPage21` |
| `LD64_GOT_LO12_NC` | `Arm64GotLoadPageOff12` |
| `NONE` | `None` |

Any other aarch64 ELF relocation fails the compile with
`Unsupported relocation type: <r_type>` instead of being dropped (fail
closed). `LDST128_ABS_LO12_NC` is deliberately left out: the applier derives
the LO12 scale from bits 31:30, which is wrong for 128-bit accesses.

## Verification

aarch64 DGX Spark host, `cargo test --release -p simple-compiler --lib -- linker:: smf`:

- before the fix: `171 passed; 2 failed` — the new specs
  `aarch64_elf_relocations_map_to_arm64_smf_types` (`r_type 283: left Plt32,
  right Arm64Branch26`) and `aarch64_elf_unsupported_relocation_fails_closed`
  (LDST128 parsed as `reloc_type: None`);
- after: `173 passed; 0 failed`.

End to end with the rebuilt seed:

| program | old seed | fixed seed |
|---|---|---|
| `print("hi")`, `seed hi.smf` / `seed run hi.smf` | SIGBUS rc 135 | `hi`, rc 0 / rc 0 |
| fn call + for loop + text concat | SIGSEGV rc 139 | `sum=45`, `smf ok`, rc 0 |

Neighbouring tests (unchanged crates): `simple-common` smf/reloc 2/2,
`simple-runtime --lib` smf/reloc/loader 112/112.
