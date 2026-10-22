# Cranelift AOT accessor visibility

Status: source repair and focused native-helper PASS. Updated-compiler adapter
gates remain pending. This is not full compiler or merge admission.

## Exact defect

The address accessor initially requested the data's Local, Hidden, or Export
linkage. `rt_cranelift_aot_define_function` nevertheless redeclares every
finished function with `Linkage::Export` before definition. The JIT-only
`rt_cranelift_define_function` also redeclares Export and is not an AOT repair.
Thus a private/scoped data address became externally callable despite its
requested linkage. This is a provider-definition contract defect, not evidence
that scoped globals are semantically public.

Actual scoped access exists: `test/fixtures/compiler/imported_globals/main.spl`
imports the provider's `pub(package) SCOPED_VALUE`. HIR directory-sibling
registration also deliberately shares declarations while retaining private
import details. `READINESS_FULL` is a different case: it is an exact immutable
private literal, transferred by value by the earlier fix without data storage.

## Current repair and capability boundary

Only Public stored globals receive an exported address accessor. Private,
Peer, Up, Internal, and Package data retain their existing storage linkage and
local direct-address operations, with no accessor generated. An external
non-public static fails with `requires visibility-preserving accessor support`.
That diagnostic reports the Cranelift backend limitation; it does not reject
the language's visibility rules or substitute a public declaration.

The accessor-definition helper independently rejects every non-Export linkage
before native calls. No Rust/C source, runtime ABI, or language visibility rule
was changed.

## Missing provider capability

A future AOT definition API must define the already declared function identity
without changing its linkage. Acceptance requires real ELF symbol assertions
for Local and Hidden functions and successful package-scoped provider/consumer
execution with one storage owner. A linkage request at declaration time alone
is insufficient evidence. Do not remove the current rejection until that
native provider contract exists and is verified.

## Verification

The focused fixture `native_cranelift_accessor_visibility.spl` creates valid
native AOT/data handles, rejects Local/Hidden/Import definition requests, then
emits a Public accessor. Its object must contain exactly the Public accessor
and no rejected accessor names. The distinct private data symbol must remain
LOCAL. This exercises real native operations, rather than a source-text check
or a fake module handle.

The fixture is compiled by the existing native combined producer with SHA-256
`67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`;
it imports the changed helper as application source, so no full compiler
rebuild is required for that focused gate.

The native fixture built three modules and executed with exit zero. Its actual
ELF symbol table contains `private_payload` as OBJECT LOCAL, `public_payload`
as OBJECT GLOBAL, and exactly one accessor function:
`__simple$global_address$v1$accepted_public`, FUNC GLOBAL. No rejected Local,
Hidden, or Import accessor was emitted. Logs and artifacts are under
`build/native_probe/imported-globals/` in the isolated
`/home/yoon/dev/simple-cranelift-text-globals-20261010` worktree:
`visibility-helper-scoped-build.log`, `visibility-helper`, and
`accessor-visibility.o`. The first probe failed source admission because its
snapshot omitted imports; the successful invocation added only the backend
and SFFI source directories, not a full compiler build.
Executable SHA-256: `d86ef59c36ddafc89ae46183b96ed1ac374a368cf9d26a70e2192e9b2e82fcb6`.
Object SHA-256: `96d25cd4cba5d254242eaa70166185069e784e6ff5d65adbb2fdff8367f5f7b9`.

Pending updated-producer gates: compile `scoped_provider.spl`, confirm Private
and Package data have no exported accessor and local reads remain supported;
compile `scoped_import.spl` and require the explicit capability diagnostic;
rerun the public cross-module storage fixture; complete all mandatory full
compiler/runtime/MCP checks. Existing successful checks from earlier roots
are not rerun merely to relabel them as evidence for this correction.
