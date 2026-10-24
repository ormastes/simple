# Darwin native action identity rejected external compilers

The P2 compiler built from source 3779e0cebf9907a9838e7347a6702506bd0b860f
compiled and linked native Hello, then refused publication with
`invalid-native-action-input-identity`. Its compiler executable lived outside
the source checkout. The producer left that tool path absolute, while the
consumer required a repository-relative declaration and later always prefixed
the repository root. All six recorded identity digests had valid SHA-256 form.

The repair shares a tool-specific validator and resolver. Existing relative
receipts retain their contract; canonical external POSIX executables get
regular-file and bounded execute-permission checks before the existing artifact
and current-tool digest checks. Source/dependency path validation is unchanged.
No receipt schema or runtime ABI changes are introduced.

Qualification is pending. The first focused native action test linked, but
failed earlier relative admission because persisted manifest bytes were
corrupted by a separate packed-byte iteration defect. Its source/runtime/tool
snapshots and process cleanup checks passed. Retain that failed evidence under
release-phase2-review/build/verify/native-identity-cycle2; do not interpret the
linked fixture or original rejected Hello output as an admitted build.
