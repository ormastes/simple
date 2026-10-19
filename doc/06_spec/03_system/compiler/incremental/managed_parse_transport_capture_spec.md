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

Transport is an explicit serialized parser-owner operation. This spec does not
enable worker warning admission or qualify the pending V2 parent/worker path.
