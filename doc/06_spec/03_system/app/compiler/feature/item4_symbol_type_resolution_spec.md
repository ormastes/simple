# Selected ELF definition type

Authored companion; execution and canonical docgen UNRUN.
Source: `test/03_system/app/compiler/feature/item4_symbol_type_resolution_spec.spl`.

Three scenarios cover actual ELF symbol conversion, winning strong-versus-weak
type in both object orders, and retained type during common-storage coalescing.
They exercise the production resolver. Full-link RV64 TLS acceptance separately
checks how the selected type affects actual relocation and output behavior.
