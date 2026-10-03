# Managed native runtime and tool binding

Status: patch implemented; native and SSpec execution UNRUN.

The managed Phase 4 environment requested sealed tool/runtime authority, but
hosted native compilation still had independent SIMPLE_CC, CC, linker, CRT
discovery and runtime-source/archive selection routes.

Sealed authority selectors activate the strict path through the canonical
SOSIX `native_tool_strict_requested_v1` predicate. The snapshot-capture flag
alone does not activate compiler consumers. The tool authority is owned by
`native_tool_authority_v1.spl`. Runtime input
binding is in `native_runtime_authority_v1.spl`; it decodes the existing source
and runtime snapshot formats instead of producing a second admission policy.

LLVM retains fresh C runtime compilation. The source snapshot binds the
`src/runtime/` tree, including headers, before compilation. Managed builds do
not consume the legacy runtime object cache. Successful generated runtime
objects receive process-owned descriptor/hash bindings and must all be present
at the final link. Cleanup releases only these generated objects. An optional
native-all archive remains governed by the existing bundle selector and must
match the sealed runtime snapshot; core-C never acquires it ambiently.

Cranelift retains the existing named archive-provider selection. The selected
absolute archive paths must exist in the sealed runtime snapshot with matching
digests. Wrong roots, missing providers, substitutions and metadata changes
fail admission. The runtime `none` sentinel requires this invocation's bound
generated runtime objects.

Strict Linux links use admitted clang and an absolute `-fuse-ld` path, avoiding
the old ambient gcc CRT discovery. Strict Windows MSVC uses the admitted
linker and the sealed LIB projection without vswhere/cmd discovery. Windows GNU
uses the admitted clang driver and absolute linker path. Driver overrides in
extra flags are rejected. Legacy discovery remains outside managed mode.
The managed extra-argument vocabulary is closed to the generated origin rpath;
response files, driver configs and forwarding options fail closed. Runtime and
entry inputs retain `.c` extensions; runtime compilation also specifies C11,
so clearing ambient CL/_CL_ preserves their C language mode.
LLVM symbol extraction uses admitted `nm` through direct argv; native object
compilation and entry-shim construction propagate its errors. Ambient
`SIMPLE_LINK_OBJECTS` providers are rejected instead of silently linked.

Files are hashed at admission and terminal validation. Cached bindings use
descriptor metadata for intermediate checks; they do not provide an execution
file-descriptor lease against a hostile writer. SDK/CRT libraries implicitly
selected by the admitted driver remain covered by pinned tools and sealed
SDK/library environment paths, not individual SDK file hashes. This is not a
fully hermetic SDK supply-chain claim.

Added `test/01_unit/compiler/backend/native_runtime_authority_spec.spl` covers
both canonical row formats, exact provider paths on Unix/Windows, wrong and
missing providers, traversal/link aliases, invalid strict mode without ambient
C fallback, and generated-object omission/replacement. The sibling tool-owner
spec covers missing/wrong/mutated executable authority.
Sticky mutation/restore checks run in isolated child fixtures so they cannot
poison the test runner's invocation registry.

Validation: focused `git diff --check` passed. Native execution, SSpec, Linux
clang compatibility, Windows MSVC/GNU links, compiler/lib checks and MCP smoke
remain UNRUN pending an admitted executable. Do not treat this patch as a
managed Phase 4 PASS or deployment receipt.
