# Optional gzip collection payload provenance

Status: candidate implementation; TEST_BLOCKED (2026-11-03).

The original `val header = gzip_header_parse_at(data, pos); if header == nil:
return nil` form lost the optional array payload owner before indexing or
length dispatch. Commit 8047804aa5d changed gzip to explicit typed match
bindings; that is a library workaround, not a compiler repair.

The pure-Simple MIR candidate adds `optional_collection_receiver_payload_v1`.
Only a declared Optional<Array>, Optional<Slice>, or Optional<Dict> admits the
route. It evaluates the receiver once, emits a presence branch, terminates the
nil branch after panic, and extracts only in the Some block. It retains the
payload HIR type and existing runtime collection metadata. Index and length
projection use this shared owner; nominal/custom owners retain their paths.
No gzip API or workaround was removed before producer qualification.

The exact and adjacent native fixture is
`test/02_integration/compiler/backend/probe_optional_collection_provenance.spl`,
driven by `optional_collection_provenance_native_spec.spl` in the same directory.
Its expected count is 15, including original guarded optional function results,
single evaluation, present empty arrays, nil paths, byte width, dictionary
index/length, and erased reader conversions. Those are authored checks, not
executed PASS counts. The test disables stub fallback and checks build and run.

Verification: scoped whitespace/static review only. No admitted self-hosted
CLI exists in this Windows recovery environment; the tracked Rust seed and
frozen diagnostics are not acceptable substitutes. Native fixture, compiler/lib
checks, core runtime and MCP native smokes remain unrun. Candidate must remain
draft and both bug records remain open pending qualified execution and review.
