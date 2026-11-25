# Compatibility aliases retained unreachable targets

- **Status:** ELF fixed and regression passed; Mach-O Stage 4 projection and COFF/native Windows remain pending
- **Observed:** referencing one generated compatibility alias retained the whole `_stubs.o` text section, pulling unrelated aliases and their optional unresolved targets into strict links.
- **Cause:** generated assembly placed every trampoline in the same executable section, defeating linker section garbage collection.
- **Fix:** emit one executable section per generated symbol on ELF/COFF targets and enable Mach-O symbol subsections; native Windows keeps its existing C `-ffunction-sections` path. Only the ELF path is currently qualified: Mach-O request projection does not yet dead-strip these atoms, and COFF has directive-only evidence.
- **Regression:** a Linux linker probe uses one alias while an unreferenced sibling jumps to a nonexistent target; `--gc-sections` must discard the sibling and produce a runnable binary.
- **Remaining portability risk:** native-Windows strict compatibility candidates still use the separate C stub-body path instead of signature-preserving trampolines; add a Windows link/run regression before claiming parity.

## Verification note 2026-11-25 (code inspection; execution environment-blocked)

Re-inspected on release/1.0.0 @ 1980cba75de (Windows host):

- The per-symbol-section fix now exists for all three targets in the seed's
  stub generator: ELF `.text.stub_<i>` and COFF `.section .text$stub_<i>,"xr"`
  via `alias_gc_section()`
  (`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:132-136`),
  Mach-O `.subsections_via_symbols` (stubs.rs:126), and the compat-alias path
  emits `.section .text$compat_alias_<i>,"xr"` (stubs.rs:1478).
- A pure-Simple linker behavioral spec now covers the previously
  directive-only side: `test/01_unit/compiler/linker/coff_macho_alias_subsection_gc_spec.spl`
  (#4647) pins COFF `$` subsection GC and Mach-O `-dead_strip` atom
  elimination. NOT executed in this session: the deployed seed binary's
  semantic phase rejects the current test runner's
  `@representation_boundary` decorator, so no spec can run via
  `bin/simple.exe test` on this host.
- Still open, unchanged: a Windows link/run regression through the seed's
  native-Windows C stub-body path (the "Remaining portability risk" above),
  and executed Mach-O Stage-4 projection evidence (macOS-only). Status line
  above remains accurate; this note records that the COFF/Mach-O emission
  and pure-Simple-linker spec coverage have since landed in source.
