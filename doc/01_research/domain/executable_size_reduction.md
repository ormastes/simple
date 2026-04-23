# Executable Size Reduction - Domain Research

Codex findings, 2026-04-23.

This research reuses the existing repository domain study in `doc/01_research/domain/binary_size_optimization_across_languages.md`.

## Applicable Prior Art

The relevant cross-language pattern is consistent: compile code and data into independent sections, let the linker garbage-collect unused sections, and avoid force-loading static archives unless every member is required. Rust release profiles add size-sensitive codegen choices such as LTO, one codegen unit, panic abort where compatible, and symbol/debug stripping for distributed binaries.

For C/C++ and native generated objects, `-ffunction-sections`, `-fdata-sections`, and ELF `--gc-sections` are only effective when archives are linked normally. `--whole-archive` and Mach-O `-force_load` intentionally retain entire archive member closures and should be reserved for cases where precise symbol roots are unavailable.

## Local Mapping

The Simple native-build path already has section-level compilation and ELF section GC. The domain fix is therefore not a new optimizer; it is removing the force-load blocker and replacing it with explicit root retention for runtime symbols that are not visible as ordinary direct references.
