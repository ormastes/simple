# Hosted Mach-O image construction

Source: `test/03_system/app/compiler/feature/item4_linker_macho_hosted_spec.spl`.
Requirements: ITEM4-REQ-004 and ITEM4-REQ-006.
Evidence: **UNRUN**. This is a manually maintained intent mirror, not generated
SPipe output. Docgen, sspec-maintain, branch coverage and native execution await
an admitted pure-Simple runtime. Sidecars: N/A.

Use actual clang MH_OBJECT inputs and ld64.lld dylibs from
`test/fixtures/linker/macho`. The production entry is `macho_hosted_link`; tests
do not invoke a stand-in linker. All helper names use `item4_macho_hosted_`.

| Scenario | Action and meaningful oracle |
|---|---|
| Imported TLV descriptors | Link real x64 TLV and ARM64 TLVPPAGE relocations; check exact GOT displacement, ADRP and LDR bytes, plus nonempty binding stream. |
| Page signature | Sign one zero page; independently read big-endian SuperBlob/CodeDirectory fields and compare all 32 hash bytes with the .NET SHA-256 reference. |
| x64 hosted main | Link actual imported call/GOT/data pointer and local pointer; inspect PIE, LC_MAIN, dyld path, rpath, UUID, exact call displacement, local pointer, complete eager binding operands and rebase bytes. |
| Archive definitions | Compare direct and real BSD archive selection byte-for-byte; inspect local call, GOT target and empty bind program. |
| TLS kind mismatch | Mutate a real TLV relocation to GOT_LOAD; reject an ordinary-data interpretation of a TLS provider. |
| Unsupported local TLS / rpaths | Reject local template definitions explicitly, missing @rpath search paths and duplicate paths. |
| Signature admission bounds | Reject missing signature storage, negative code extent and embedded NUL identifier. |
| ARM64 hosted main | Link GOT page references and imported branch; inspect instructions, branch stub and actual embedded-signature magic. |
| Missing/incompatible/oversized | Reject absent providers, foreign CPU dylibs and too-small image budget. |

The dylib TLS fixtures deliberately leave `__tlv_bootstrap` dynamically resolved
for a real Darwin host. Their inspection establishes format provenance only.
No fixture is claimed to have executed. LC_MAIN system startup, provider closure,
signature trust and imported TLS runtime behavior require separate Darwin tests.

Open implementation gates: local TLS/template/init, compact/DWARF unwind,
weak/interposition semantics, reexport resolution, hosted ARM64 ADDEND pairs and
an explicit executable-export contract. The full Mach-O item remains incomplete.
