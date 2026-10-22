# Explicit external file compatibility

Authored scenario manual; all 11 cases **UNRUN**. Source-derived inventory, not generated runtime evidence.

Executable: `test/02_integration/io/external_file_io_spec.spl`. Existing std.spec assertions and real OS file APIs are used; no fake provider or new runner.

1. retains UTF-16 file bytes before decoding a non-BMP scalar and NUL.
2. rejects malformed UTF-8 in the migrated legacy file API.
3. encodes outbound file text in the requested byte order.
4. returns exactly one external character from a file and rejects multiple scalars.
5. retains file facade replacement semantics for a symbolic link.
6. reads and writes declared positional text without changing neighboring bytes.
7. appends destination-encoded bytes through the real append descriptor.
8. uses the shared codec for actual FileHandle text operations.
9. preserves atomic and exclusive UTF-8 providers and rejects unadmitted output formats.
10. keeps legacy positional writes write-only and does not widen creation mode.
11. keeps empty legacy appends successful without creating files or parents.

Only the eleven FILE cases were selected from the mixed historical transport suite. Five TCP cases and all network imports are excluded. The already-landed four-case pure facade suite is unchanged. Permission/symlink cases still require their supported platform; no executed portability evidence is asserted.

Logical byte limits do not establish total RSS. Native provider identity, close/refcount behavior, class alias/private-field semantics, OOM, partial-write fault injection, performance and canonical docgen remain open; see the file session guide and provider/performance tracking note.
