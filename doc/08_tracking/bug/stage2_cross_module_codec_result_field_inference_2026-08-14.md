# Stage 2 loses cross-module codec result field types

Status: provider workaround applied; compiler fix remains open.

Admitted compiler:

- path: `/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- SHA-256: `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`
- sanity evidence: `status=pass`

Reproduction: compiling `src/app/provider_cli/native_provider_v1.spl` through
the admitted `native-build --entry-closure --emit-archive --no-mangle` path
failed while accessing `.ok` on the result of
`encode_provider_query_result_v1`:

`hir: Unsupported feature: cannot infer field type ... struct
'ProviderQueryWireWriteV1' field 'ok'`

Explicitly annotating cross-module codec results is the safe provider-side
fix. The compiler should eventually preserve the declared return type through
cross-module calls without requiring redundant local annotations.
