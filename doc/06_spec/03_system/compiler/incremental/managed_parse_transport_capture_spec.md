# Parser-owned warning transport capture

Executable: `test/03_system/compiler/incremental/managed_parse_transport_capture_spec.spl`.
REQ-IM-006/007/016, NFR-IM-004. Status: authored, runtime/docgen UNRUN.

1. Parse a real enclosing-local write through ordinary and transport capture.
   Both rich ASTs contain main, neither reports a parse error, ordinary cache
   capture stays empty, and transport yields a restorable nonreusable payload
   with the pre-desugar warning at the independently expected source line.
2. Take twice and verify no stale payload or warning escapes. Parse malformed
   source after an untaken warning capture and verify that prior state is lost.
   A later clean module can produce a reusable payload without inherited warning.
3. Attempt ordinary take of a transport capture; require empty output and reset.
4. Parse a single module containing both a captured-write warning and an
   independent syntax error. Retain its current warning despite an empty blob.
5. Close a parser-owned streaming scope, then consume both warning text and
   the restorable payload. Both transport strings are explicitly promoted as
   separate roots before scope closure; borrowed scopes remain caller-owned.

Transport is an explicit serialized parser-owner operation. This spec does not
enable worker warning admission or qualify the pending V2 parent/worker path.
