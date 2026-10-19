# File text sessions

Authored scenario manual; all 20 cases **UNRUN**. Source-derived inventory, not generated runtime evidence.

Executable: `test/02_integration/io/file_text_session_spec.spl`. Existing std.spec assertions and real OS file APIs are used; no fake provider or new runner.

1. keeps ordinary File and runtime reads in internal UTF-8 without caller conversions.
2. stores UTF-16BE with one required BOM across repeated writes and automatically decodes it.
3. isolates two simultaneously open sessions with opposite byte order.
4. uses distinct input and output encodings from one stored session codec.
5. rejects invalid UTF-8 before exposing internal text and closes the failed session.
6. rejects a truncated UTF-16 surrogate pair at EOF with its byte offset.
7. honors declared byte order and forbidden BOM without autodetection.
8. distinguishes exact input budget from overflow and makes overflow terminal.
9. rejects oversized output before writing and leaves the session usable.
10. validates convenience output before truncation and preserves legacy empty append.
11. uses byte-framed positional reads and emits no interior BOM on positioned writes.
12. refuses unsupported required-BOM append before opening or creating a file.
13. retains borrowed byte ownership and ordinary positional UTF-8 behavior.
14. handles a surrogate pair split across the bounded provider read chunks.
15. makes the ordinary owning FileHandle terminal after a failed text read.
16. rejects one-shot UTF-16 append at an odd byte position without writing.
17. treats appended U+FEFF as content with Forbid on a nonempty file.
18. shares terminal close state across class aliases without closing a later session.
19. closes owning write failures and positioned read failures on real descriptors.
20. strictly decodes ordinary lines and makes malformed line consumption terminal.

The historical seventeen cases are retained. Three added scenarios test shared class close state, real read-only write/write-only positioned-read failures (including ordinary FileHandle), and strict bounded line routing with the next-byte cursor preserved. The line overflow, failed-seek and failed-close allocation/provider injection paths still lack admitted execution.

Logical byte limits do not establish total RSS. Native provider identity, close/refcount behavior, class alias/private-field semantics, OOM, partial-write fault injection, performance and canonical docgen remain open; see the file session guide and provider/performance tracking note.
