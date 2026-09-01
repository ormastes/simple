# Compatibility aliases retained unreachable targets

- **Status:** ELF fixed and regression passed; Mach-O Stage 4 projection and COFF/native Windows remain pending
- **Observed:** referencing one generated compatibility alias retained the whole `_stubs.o` text section, pulling unrelated aliases and their optional unresolved targets into strict links.
- **Cause:** generated assembly placed every trampoline in the same executable section, defeating linker section garbage collection.
- **Fix:** emit one executable section per generated symbol on ELF/COFF targets and enable Mach-O symbol subsections; native Windows keeps its existing C `-ffunction-sections` path. Only the ELF path is currently qualified: Mach-O request projection does not yet dead-strip these atoms, and COFF has directive-only evidence.
- **Regression:** a Linux linker probe uses one alias while an unreferenced sibling jumps to a nonexistent target; `--gc-sections` must discard the sibling and produce a runnable binary.
- **Remaining portability risk:** native-Windows strict compatibility candidates still use the separate C stub-body path instead of signature-preserving trampolines; add a Windows link/run regression before claiming parity.
