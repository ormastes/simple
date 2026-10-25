# Common C4 resource account owner

The HIR constructor/query and runtime scope-reader prerequisites need the same
invocation account as MIR. The selected retained account-owner revision 3 moves
the canonical implementation to `compiler.common.loop_resource_account_v1` and
retains the MIR path as a direct `pub use` compatibility import.

The common implementation is byte-identical to the 153-line MIR owner landed in
PR #4618: SHA-256
`b9fbf6cc967f312c37e471ee65cb89c7cfa779ce12d46361fbda4ba760d69bcd`.
The five account types and existing validator refer to this single owner; no
adapter, second account, cost model, limit or reservation behavior is introduced.
The MIR facade matches the selected immutable packet image, SHA-256
`a7eac01fd4ccd29e8091a1ed45c278d65d52349c2f44af2a14cba127123075ba`.

Authority: `hir-source-admission-implementation-v1/account-owner-component/revision3`
under the external packet root recorded in
[the foundation provenance](c4_account_provider_foundation_v1.md).
Astra independently compared the exact moved bytes and direct re-export.

This dependency relocation does not establish actual runtime class aliasing or
native struct transport. The existing account/provider and builder scenarios
remain UNRUN. The scope facade's separate Stage 2 diagnostic reached HIR then
failed in native MIR; evidence is retained at
`/tmp/c4-scope-read-pure-20261025/dict_scope_facade.log`. No runtime, source-authority,
physical allocation or full C4 PASS is claimed. HIR constructor hooks and the
runtime reader are separate changes.
