# Frozen-Phase-2 parity instances, round 2: ctx_postings AOT ptr-to-double; CommandState ambiguous field owner; HttpRequestParserV1 missing native trait impl (2026-11-16)

**Status:** OPEN (candidate codegen/resolution; source workarounds not yet identified for these three)
**Area:** stage2 candidate AOT lowering + MIR resolution
**Context:** after #9735 (method dedup), #9770 (Trd rename), #9803 (two MIR
workarounds), the mcp stage2 build clears MIR entirely (371/372 units) and
the fleet's remaining failures are these three candidate-only defects.

## Instance 1 — mcp build: ctx_postings AOT lowering

```
reason: AOT compile error in app.mcp.ctx_postings: compile error:
unsupported LLVM value conversion from ptr to double
function=app.mcp.ctx_postings.ctx_scores_by_postings value=%l292
reason: ... ctx_scores_by_scan value=%l356 ... at=unknown location
error: build failed: 1 failed, 371 ok of 372 unit(s)
```

`ctx_scores_by_postings` (src/app/mcp/ctx_postings.spl:157) is plain f64 math
over CtxPosting fields; no raw-pointer source construct. The candidate's LLVM
lowering typed a value as ptr where double is required (likely an f64 struct
field load through a wrong-slot GEP). Diagnostic capsule: preserved under
the build's simple-aot-diagnostic-* dir for the module. Owner ask: locate the
ptr-typed f64 load and add a lowering assertion that fails with the source
location instead of "unknown location".

## Instance 2 — caret build: CommandState ambiguous field owner

```
MIR lowering error: ambiguous struct/class field owner 'CommandState':
no module-qualified type provenance
at src/lib/nogc_sync_mut/io/windows_stdin_command_owner_v1.spl:514:51
```

A field access whose receiver type 'CommandState' resolves without
module-qualified provenance (another bare-name collision class — same
disease as the test_extended structs, at the field-owner level). Owner ask:
find the second CommandState-shaped declaration in the caret closure and
either qualify or rename; add a provenance requirement to the registry.

## Instance 3 — caret build: HttpRequestParserV1 missing native trait impl

```
MIR lowering error: missing native trait implementation:
lib.nogc_sync_mut.http_server.request_parser::HttpRequestParserV1 for
at src/lib/nogc_sync_mut/http_server/server.spl:303:17
```

An impl exists in source (the seed builds this closure) but the candidate's
native trait dispatch does not see it — related class to #9359 Regression 1
(AttrOwnerV1 object-safety, fixed near #9563). Owner ask: re-run the
object-safety/native-trait sweep over http_server.request_parser.

## Note

These are the same class upstream's frozen-Phase-2 workaround lane is
clearing one module at a time (cf. 9ad81615fc1, #9360). Each fixed layer
exposes the next; the mcp/test_runner tool binaries and the caret suite are
the current verification surfaces.
