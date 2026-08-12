# Native-build SIGSEGV `call 0x0` — mechanism hardened, upstream cause still open (2026-08-11)

## Summary

`native-build` on self-hosted binaries can crash with `call 0x0`-shaped SIGSEGVs.
The mechanism was traced to `src/compiler/70.backend/backend/native/native_elf.spl`
at the three architecture emitters (`emit_elf_x86_64`, `emit_elf_aarch64`,
`emit_elf_riscv64`). Each builds a `sym_name_to_idx: Dict<text, i64>` map while
walking data labels, extern symbols, and function names, then resolves each
relocation's `reloc.symbol_name` through that map. The lookup silently
defaulted to index `0` when the name was missing:

```
var sym_idx = 0
if sym_name_to_idx.contains(reloc.symbol_name):
    sym_idx = sym_name_to_idx[reloc.symbol_name]
```

## Correction to the original mechanism description

The original title/description assumed the fallback produced a genuine
null/`STN_UNDEF` target ("call to 0x0"). Reading the surrounding code shows
that's not quite right: the final ELF relocation symbol index written out is
`symbol_index: sym_base + sym_idx` (or `sym_base_a` / `sym_base_r` on the other
two arches), where `sym_base = 1 + num_content_sections` accounts for the null
symbol-table entry plus section symbols. So `sym_idx = 0` does **not** point at
ELF's real `STN_UNDEF` (index 0 of the whole symtab) — it points at
`sym_names[0]`, i.e. whatever symbol happened to be registered *first* in that
function's local `sym_name_to_idx` map (typically the first rodata data label,
or the first extern symbol if there's no rodata). In other words, the silent
fallback doesn't null out the call target — it aliases it to an arbitrary,
unrelated, already-resolved symbol. Depending on what that first-registered
symbol's address is, this can manifest as a call to address 0 (if the aliased
symbol itself resolves near zero, e.g. an unresolved extern), a jump into the
middle of unrelated data, or a call into the wrong function entirely — all
without any diagnostic. This is consistent with, and a superset of, the
originally observed `call 0x0` symptom.

Either way, `sym_idx = 0` from this fallback is never a legitimate "no
relocation needed" / "intentionally unresolved" sentinel in this code path —
every `ElfReloc` pushed here corresponds to an actual instruction operand that
must resolve to a real symbol. There is no code path in `emit_elf_*` where a
relocation is expected to reference a symbol absent from `sym_name_to_idx`.

## Fix landed (this session)

Hardened all three fallback sites from a silent wrong-symbol alias into a hard
build-time `panic(...)` naming the missing symbol, so a bad binary is never
silently produced:

```
if not sym_name_to_idx.contains(reloc.symbol_name):
    panic("native ELF (x86_64): relocation references unknown symbol '{reloc.symbol_name}' -- symbol was never registered in sym_name_to_idx (would silently emit a call to the wrong symbol)")
val sym_idx = sym_name_to_idx[reloc.symbol_name]
```

(same shape at the AArch64 and RISC-V sites, `panic(...)` is the idiomatic
fatal-error builtin used elsewhere in `70.backend/backend/**`, e.g.
`cranelift_codegen_adapter.spl:569,1053`, `isel_x86_64.spl:634,642`).

This converts a silent miscompilation into an immediate, named build error —
strictly safer than the previous behavior since `sym_idx = 0` was never a
legitimate case here. It does **not** fix the underlying defect: something
upstream still fails to register a symbol name into `sym_name_to_idx` before a
relocation referencing it is emitted for `func.relocations`. Likely
candidates worth checking next (not yet investigated — would require a
debug-symbol build + trace, out of scope for this read-only session):
forward-declared functions whose body is emitted before their name is added
to `ordered_funcs`/`module.extern_symbols`, generic-instantiation call
targets, or a relocation whose `symbol_name` uses a different naming
convention (e.g. mangled vs. unmangled) than what was registered.

## Status

- Mechanism: understood and corrected (silent misalign -> loud `panic`).
- Upstream cause (why a symbol goes missing from `sym_name_to_idx`): still
  UNKNOWN. Needs a debug build that can reproduce the missing-symbol case and
  print `reloc.symbol_name` plus the caller's context before this panic fires.
- No build/test was run to verify this change (host under heavy load,
  restricted to static source reading per session instructions). The edit is
  purely defensive (replaces a silent bad value with a loud error) and touches
  no other control flow, so risk of regressing a currently-passing build is
  low, but it has not been empirically confirmed.
