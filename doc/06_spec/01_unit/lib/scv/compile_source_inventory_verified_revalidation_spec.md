# Verified inventory revalidation

Executable: test/01_unit/lib/scv/compile_source_inventory_verified_revalidation_spec.spl

All six criteria are UNRUN. Real filesystem publication and initial full decode
precede successful trusted-helper calls. `std.spec.step` labels below correspond
to the executable operations and assertions. Each fixture removes its owned
temporary cache before asserting outcomes.

| Requirement | Executable steps | Required result |
|---|---|---|
| REQ-SCV-REVALIDATE-001 | Publish and fully decode one valid inventory entry; Compare full and verified revalidation against decoded fields | Both accept the same digest; generation 7, one source identity, content digest and provider digest survive full decoding. |
| REQ-SCV-REVALIDATE-002 | Publish and authenticate the initial pointer and generation; Change CURRENT and require cursor supersession rejection | Actual CURRENT mutation succeeds; helper returns `publish-cursor-superseded`. |
| REQ-SCV-REVALIDATE-003 | Publish and authenticate the original immutable generation; Corrupt the generation and require a fresh hash rejection | Same pointer with changed blob returns `inventory-generation-invalid`. |
| REQ-SCV-REVALIDATE-004 | Supply a malformed pointer and digest without a published generation | Invalid digest syntax returns `inventory-pointer-invalid`. |
| REQ-SCV-REVALIDATE-005 | Publish and authenticate a generation then supersede its cursor; Restore the pointer and require the next locked validation to succeed | First call rejects, next call succeeds after actual restoration, demonstrating ordinary rejection unlock. |
| REQ-SCV-REVALIDATE-006 | Authenticate a nonempty inventory and create a distinct valid digest; Reject the mismatched digest without accepting the current pointer | Supplied digest passes the canonical 64-hex validator, differs from the published digest, and is rejected as `inventory-pointer-invalid`. |

This does not qualify concurrent publication/crash behavior or decoder call count.
Those require the real refresh-owner diagnostic described in packet REVIEW.md.
