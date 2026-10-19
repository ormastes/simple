# Nullable file reads

Authored scenario manual; all 4 cases **UNRUN**. Source-derived inventory, not generated runtime evidence.

Executable: `test/02_integration/io/file_handle_nullable_read_spec.spl`. Existing std.spec assertions and real OS file APIs are used; no fake provider or new runner.

1. keeps native read failures distinct from EOF through all text and byte facades.
2. preserves successful EOF and reports a short exact read separately.
3. leaves a borrowed descriptor open and preserves partial-read cursor semantics.
4. rejects negative requests without consuming the descriptor.

Borrowed cases open and close their descriptor through existing SFFI, without reaching into FileHandle private fields. The owned-handle and borrowed-descriptor cursor oracles are separate actual calls. Nil provider failure, present-empty EOF and UnexpectedEof remain distinct.

Logical byte limits do not establish total RSS. Native provider identity, close/refcount behavior, class alias/private-field semantics, OOM, partial-write fault injection, performance and canonical docgen remain open; see the file session guide and provider/performance tracking note.
