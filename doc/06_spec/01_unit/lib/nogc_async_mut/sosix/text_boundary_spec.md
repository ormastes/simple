# SOSIX shared text boundary — authored manual

Source: `test/01_unit/lib/nogc_async_mut/sosix/text_boundary_spec.spl`. Nine scenarios, all UNRUN; this is not generated runner evidence.

1. Exact UTF-8/NUL bytes and multilingual/empty controls.
2. Invalid UTF-8 typed kind and byte offset; overlong/truncated rejection.
3. NUL/environment-key rejection and valid controls.
4. Exact output bytes including NUL.
5. Explicit UTF-16 text and surrogate-pair character conversion through shared codec.
6. Malformed UTF-16 and unknown-format rejection without byte mutation.
7. Separate UTF-8/UTF-16 stream carry.
8. All split positions and truncated final scalar.
9. Actual resolver-result admission before trim, empty/multiple/relative/NUL rejection and precise invalid-byte witness.

Requirements UTF8-SOSIX-01..05. The reused codec cases do not constitute new codec implementation or native Char-layout qualification.
