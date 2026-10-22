# Pure external-text error/conversion facade scenarios

Authored manual for `test/02_integration/io/external_text_io_spec.spl`; **UNRUN**, not generated execution evidence.

1. Supply unknown metadata with malformed bytes and observe the original nested UnknownEncoding error at -1. Admit malformed UTF8 as an external value, then reject conversion at the exact byte offset.
2. Encode A plus NUL into UTF16LE with a required signature; compare FF FE 41 00 00 00. Mutate a returned byte copy and confirm the encoded value is stable, then decode the exact original internal bytes.
3. Reject malformed internal provider text on output; reject malformed legacy UTF8 input with a rendered byte-offset diagnostic. Preserve NUL on valid legacy input.
4. Render Transport, Io, Unsupported and Native errors through the existing helper. Inspect the wrapped transport kind and source cause afterward to confirm rendering did not replace typed details.

The four cases invoke real pure facade APIs. They create no files or sockets and do not establish real transport errors, provider allocation-failure behavior, native ABI/private-field enforcement, or performance. Those remain separately gated.
