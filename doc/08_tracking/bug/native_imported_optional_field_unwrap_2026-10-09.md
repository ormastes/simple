# Imported optional aggregate field loses unwrap ownership

Status: fix prepared; updated-producer execution pending.

The admitted Linux Phase 2 producer SHA256
`2f34befeaca05b0cd4e389f4cda2e0d1558e15a8342f9b60f7fbacfa528830ae`
rejects LSP MCP `result.value.unwrap()` and the isolated two-module fixture
`test/fixtures/native/optional_struct_field/main.spl` with an unresolved
`unwrap` at MIR. The fixture imports a function returning an Envelope whose
value field is `Payload?`; Payload has two distinct fields so execution must
prove the second-field value `7`, not merely successful linking.

Baseline: actual native build with `SIMPLE_BOOTSTRAP=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, LLVM one-binary mode, entry closure, and the
producer-bound core-C capsule. Log `/tmp/lsp-option-field-probe-import.log`.
Same-module direct construction and typed-parameter probes passed MIR;
imported return provenance reproduces the actual failure.

Owner candidate: `remember_field_projection_provenance` in
`50.mir/_MirLoweringExpr/expr_dispatch.spl`. The declared field table already
carries Optional, but the projection copied only Named/Array/Slice type notes.
An Optional projection now retains its declared HIR type so existing
Option-only method dispatch and nil panic behavior remain authoritative.
No name-based unwrap fallback or runtime stub is introduced.

Required verification: rebuild the producer, build/run the two-module fixture
and assert exact `7\n` with exit zero; then build and exercise real LSP MCP.
If the updated fixture still fails, keep that failure visible and investigate
upstream imported field registration; this draft does not constitute PASS.
