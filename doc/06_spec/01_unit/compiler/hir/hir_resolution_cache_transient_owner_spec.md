# Streaming HIR resolution cache ownership

Executable specification:
`test/01_unit/compiler/hir/hir_resolution_cache_transient_owner_spec.spl`.
Requirement: REQ-HIR-CACHE-SCOPE-001.

## Retain resolution facts across modules

1. Create one frozen surface registry and a reusable HIR lowerer.
2. Open a transient scope and populate re-export, name, explicit dependency,
   package, payload miss and glob miss caches.
3. Pause the scope, promote the resolution cache roots, and end the scope.
4. Check native array liveness before probing the retained hash chains. The
   missing re-export must still resolve to its cached negative result, and
   projected positions and dynamic text must retain their exact values.
5. Begin another module, append a new re-export result in a second transient
   scope, promote, and end that scope. Both the old and new rows must survive.

## Reject an invalid promotion boundary

Calling the cache promotion helper outside a paused transient scope must
return false.

## Reset importer-owned enum rows

After `begin_module`, the prior importer's enum-owner row array must be empty.

## Native bootstrap regression

Compile `test/fixtures/hir_resolution_cache_scope/main.spl` with an admitted
macOS arm64 Stage 2 using its bare positional `native-build` route and an
isolated cache. The executable must print `hir-resolution-cache-scope-ok` and
exit zero. `--source` routes this bootstrap CLI through its Rust FFI and is
not acceptable as evidence of the pure-Simple importer.

## Evidence status

The pre-fix macOS 30-module driver-public-API reduction stalls after one HIR
module; a native sample identifies `reexport_root_memo_lookup`. The patched
reduction passes this boundary in 13 ms, then exits with incomplete-closure
import diagnostics. The three-file native fixture compiles and runs with
the expected marker and exit 0 (2026-09-21, macOS arm64).

The separate `test/fixtures/hir_resolution_cache_scope/transient_lifetime.spl`
tests the runtime contract for two scopes, retained arrays and appended text.
Its first native compilation is blocked by capsule `identity-invalid`, so
no lifetime execution PASS is claimed. The actual HIR SSpec is unexecuted;
canonical Stage 3 is pending. This authored manual does not claim that the
compiler-only Stage 2 can execute SSpec or generate this manual. Exact
commands, hashes, and limitations are in Round 28 of the linked bug report.
