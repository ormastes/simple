# Seed: struct definitions resolved by bare name — `ElfSymbol` shadowing

- Found: 2026-11-06, XRay PR5b, building a native object through the full
  pure-Simple CLI graph (`cli_compile`) under the Rust seed.
- Status: open. Workaround: `test/fixtures/xray/xray_native_cli_compile_driver.spl`
  declares a main-file `ElfSymbol` with `native/elf_writer.spl`'s exact fields.

## Symptom

`class ElfSymbol has no field named sym_bind` while writing the ELF symbol
table of ANY non-empty native object (not XRay-specific). The full CLI graph
also loads `70.backend/backend/linker/elf_parser.spl`, whose `ElfSymbol` has
different fields; the seed keys struct definitions by bare name, so the last
registration wins and `native/elf_writer.spl`'s constructor builds the wrong
struct. Imported-module structs are not added to the overload fallback, so a
main-file twin is the only override.

## Fix direction

Key struct definitions by module path in the seed (same class as
`seed_enum_variant_bare_name_last_registration_wins_2026_10_19`), or rename one
of the two `ElfSymbol` structs.
