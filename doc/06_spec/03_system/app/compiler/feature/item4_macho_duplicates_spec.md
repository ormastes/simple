# Mach-O duplicate-definition policy

Six authored ITEM4-REQ-003 scenarios in
`test/03_system/app/compiler/feature/item4_macho_duplicates_spec.spl`.
**UNRUN**: manually authored manual; no admitted Simple test execution.

| Scenario | Observable behavior |
|---|---|
| Ordered strong definitions | Real x64 and ARM64 A/B inputs reverse the chosen 11/22 function and data. Independent instruction decoding follows the patched call and GOT reference and checks the direct pointer. |
| Strict rejection | Competing strong definitions fail without replacing a destination sentinel. |
| Builder/direct defaults | Ordinary NativeLinkConfig defaults permit duplicates when required explicit platform/signing flags exist; direct hosted request and static linker defaults still reject. |
| Archive fixed point | A member demanded for `_trigger` introduces a duplicate and a new `_leaf` demand. Permissive mode preserves the earlier strong definition and resolves the two-hop pointer to77; strict mode rejects. Unneeded duplicate-only archives contribute no data/GOT displacement changes in either mode. |
| Resolver precedence | Actual parsed weak/strong/common objects preserve strong over weak, defined weak over common, and first weak over later weak in both input orders. This is shared resolver coverage, not hosted weak support. |
| Common layout | Two actual common declarations retain maximum size32 and alignment32 in both orders; a one-byte-short layout limit rejects. |

Fixture provenance: `test/fixtures/linker/macho/RECIPE.md`, duplicate policy section.
Output construction is inspected without launching Darwin executables. Hosted
weak-definition support remains outside this slice. No whole-product, host,
memory qualification or timing result is inferred.

After independent runtime admission:
`<runtime> test test/03_system/app/compiler/feature/item4_macho_duplicates_spec.spl`
