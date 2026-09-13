# Runtime Optional Provider and Binary-Size Optimization — Domain Research

## Findings

### Fine-Grained Dead Stripping

Clang supports function-level sections. GNU ld documents that `--gc-sections` follows relocations from explicit roots, while `--print-gc-sections` and linker map output expose retained and removed inputs. This requires avoiding broad `KEEP`, exported-root, constructor, and `__start/__stop` patterns that unintentionally retain whole registries.

### Dynamic Dependency Admission

GNU ld's `--as-needed` emits a dynamic dependency only when it resolves a required non-weak reference at the relevant link position. Simple should additionally validate the final dependency list because command-line flags alone do not prove absence of constructors or indirect dependencies.

### Symbols and Debug Data

GNU strip distinguishes debug-only, unneeded-symbol, and all-symbol removal. Simple needs separate debug, release, and release-small contracts rather than applying destructive stripping indiscriminately.

### Exceptions, Unwind, and RTTI

Clang exposes explicit exception and unwind controls. They are safe only when closure analysis proves that no selected Simple or foreign provider throws across the boundary, requires stack unwinding, or depends on RTTI/dynamic casts. Foreign libraries that require these facilities belong in separately built provider DSOs; they must not force those facilities into the base executable.

### Python Comparison

Python's small scripts rely on a shared runtime and dynamically imported extension modules. The fair Simple script-runtime target is therefore resident/startup footprint of the base interpreter plus demanded modules, not the size of the script alone. Optional Simple facilities should follow the same demand principle while retaining stronger typed provider admission.

## Adopted Techniques

- Per-function and per-data sections.
- Linker garbage collection and retained removed-section evidence.
- `--as-needed` plus post-link dependency allowlists.
- Hidden-by-default visibility with explicit export manifests.
- Identical code folding where target/linker semantics permit it.
- Separate provider DSOs for unwind/RTTI-requiring foreign code.
- Release-small no-exception/no-unwind/no-RTTI mode only after closure proof.
- Linker map, section inventory, symbol ranking, dependency list, and size receipts for every size gate.

## Primary References

- Clang command-line reference: https://clang.llvm.org/docs/ClangCommandLineReference.html
- GNU ld options and garbage collection: https://sourceware.org/binutils/docs/ld/Options.html
- GNU binutils strip: https://sourceware.org/binutils/docs/binutils/strip.html
