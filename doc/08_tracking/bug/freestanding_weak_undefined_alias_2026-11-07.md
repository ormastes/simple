# Weak undefined symbols cannot provide freestanding alias targets

Status: fix implemented; focused cross-ELF qualification passed.

`NativeProjectBuilder::freestanding_qualified_to_bare_defsyms` classified only `nm` kind `U` as undefined. ELF weak undefined function/object kinds `w` and `v` consequently entered the definition set. When a qualified import matched such a bare name, the linker received an alias to a symbol that had no definition.

The fix classifies `U`, `w` and `v` as undefined. Defined weak symbols (`W`/`V`) remain eligible. Existing name matching and public interfaces are unchanged.

Qualification used real freestanding ELF objects produced on Windows by Clang 23.1.2 targeting x86_64 Linux, inspected by LLVM nm 23.1.5. The original production helper emitted a spurious alias and failed the assertion; the candidate rejected that alias. A real bare definition plus a qualified caller remained a positive alias control. The host harness extracted the two production methods and seven complete dependency functions; its only production-code difference was this filter line. No mirrored symbol-classification algorithm was used.

All bounded subprocess receipts reported quiescence; peak RSS was 145,764 KiB. Source/tool bindings were preserved. Retained local evidence: `build/review/seed-llvm-import/cross-elf-attempt1/RESULT.md`. A Linux unit regression also constructs the real weak-undefined object and checks the production helper.

This fixes the independently reproduced weak-undefined alias case. It does not establish the original rv64 kernel link or close the older `llvm_import_path_mangling_os_prefix_mismatch_2026-06-15` report. Canonical registration of the new subcase remains pending the normal full CLI; existing BugDB counts are unchanged.
