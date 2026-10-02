# Native child cleanup diagnostic classification

Executable specification: test/01_unit/lib/native_cleanup_diagnostic_spec.spl.
Owner implementation: src/lib/nogc_sync_mut/test_runner/child_diagnostics.spl.

Seven scenarios contain nine real assertions. They cover an authoritative
diagnostic alongside green result text, the reserved code-only line, CRLF and
whitespace, quoted source/descriptor traces, a different code sharing the prefix,
an incidental marker inside another diagnostic, and empty/green-only captures.
Only a standalone `error: NATIVE-CACHE-CLEANUP-FAILED` line, optionally followed
by a colon and reason, is the child-owner quarantine protocol.

The native process probe additionally drives an actual81-entry dispatcher at
requested80workers. A zero-exit child with the diagnostic must block pending
entry81; a child with a quoted descriptor must allow the pending entry to start.
Those fixture counts are deliberately untrusted input, not qualification evidence.

Execution status: NOT RUN. An admitted pure-Simple runtime is required; source
inspection and structural checks do not substitute for executing this spec.
