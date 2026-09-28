# Target 6 typed-HIR export SMF producer

Status: semantic SMF producer implemented; production graph publication open.

`cold_hir_export_smf_v1` takes a typed `HirModule`, its frozen-inventory
semantic seed, package and variant identities, and the reached graph's reverse
dependents. It verifies that the module name and typed ABI digest match the
seed, builds actual canonical ABI and reverse-projection payloads, and packs
them through `package_export_smf_build_v1`. The result carries a checked SMF
record and the two digests needed by cold package drafts. It does not invent
an initializer, provider, generated-source, interface archive, or action
archive receipt.

The SMF and reverse-projection builders now use the checked linear text
builder already used by the native CAS/archive path, avoiding ambiguous
`[text].join` dispatch in mixed native entry closures.

No-stub Stage2 native evidence: 310 source units compiled with zero failures;
the 275 KiB spec binary passed 2/2 examples. One example validates the exact
SMF section order, ABI digest, reverse digest, complete payload, and changed
reverse graph. The other mutates the HIR public export while retaining the old
seed and proves rejection before metadata assembly. Build peak RSS was
1,450,444 KiB; the spec process used 1,968 KiB peak RSS under a 4 GB
address-space bound.

Remaining: call this producer from the successful typed-HIR compiler path,
bind real source witnesses and post-codegen archive receipts, publish a
complete V2 package/module graph, prove warm archive reuse through the full
CLI, and run the matched native compile-time and RSS cohort. This focused
spec is not a Target 6 production cutover or performance receipt.
