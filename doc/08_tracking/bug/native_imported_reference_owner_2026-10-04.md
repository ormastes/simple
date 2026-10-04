# Imported reference signatures lose their declaring scope

Status: repair drafted; rebuilt-compiler validation pending.

The LLVM Phase 3 bootstrap fails with unresolved `RouteCapabilityScope` in
modules importing functions whose signatures contain `&RouteCapabilityScope`.
The class is declared in the function owner's module.

A two-file native reduction importing only `create_scope` and `close_scope`
fails in HIR with unresolved `HiddenScope`. Adding `HiddenScope` to the
consumer's explicit import list makes the same program compile and run,
printing `PASS imported class result` and exiting zero. Producer SHA-256:
`84c36744623a49a91f1bb108ad987431719ea5a61969ea42ed5f1e18993b5ff3`.

`imported_surface_type` projects pointers and several other composite type
shapes through the declaring module's qualified type bindings. References
instead fall through to `lower_type`, which searches the importing scope.
The repair adds parser-owned reference accessors and recursively projects
the referent while preserving reference mutability. It does not bind the
class into every importer's unqualified namespace.

Regression entry: `test/fixtures/compiler/imported_reference_owner/main.spl`.
Keep its sibling `owner.spl` when preparing a native-build source directory.
The repaired compiler must compile the functions-only import and produce
the same successful output as the explicit-type-import control. That
repaired-compiler test has not yet run. No Phase 3 or release PASS is claimed.
