# Imported struct operators miss qualified equality owners

Status: observed native RED; source repair authored; GREEN not established.

The admitted pure-Simple producer
`bf3f9b39f466576febfff5459f4cea175e93c439802543f92a8f710d11076ccb`
compiles and executes the same-module custom-equality fixture successfully.
A separate two-module fixture defines ImportedModulo.__eq__ in provider.spl,
imports that type, then compares typed parameters in main.spl. Both `a == b`
and `a != b` fail MIR lowering with `operator overload for struct ImportedModulo`.
The native RED process exited1, peak4330184KiB, quiescent1. Its log is
`build/native_probe/imported-inequality-bf3f9b39/compile-red.log` in the owned
`simple-items247-import-eq-20261020` worktree. Later array-element assertions
extend that fixture; the observed RED is pinned by its SCV source snapshot
`scv-revision-v1-6934da717f76a52f47853a52d8ff6335db87d18a698050dcaefa396c0028a1fb`.

Binary dispatch used a raw layout spelling for its method key. Imported
provider rows use a callable identity qualified by defining module. Ordinary
method dispatch already resolves the exact Named SymbolId before using
struct_owner_method_key; binary dispatch must use the same ownership rule.
The candidate adds binary_struct_owner, uses the shared key resolver, and
rejects ambiguous method rows before emitting calls. It retains the existing
MIR Struct type gate and missing-owner diagnostic; it does not guess by a
same-named provider or compare record addresses.

Three authored MIR scenarios cover demand/eager providers and a missing method
on one of two providers with the same bare type name. The native fixture covers
both operators, a user-defined relation and array-element projections. These
new candidate tests remain UNRUN. A rebuilt producer is required for GREEN.

The larger store-accounting probe independently has 11 unique operator-owner
diagnostics in 6 failed modules, reduced from the earlier 18 diagnostics in9.
Its exact five database source snapshot files match the current parent tree.
The former typed-pattern wildcard and DbPolicyConfig diagnostics did not recur;
this is compile evidence only, not full database feature acceptance.
