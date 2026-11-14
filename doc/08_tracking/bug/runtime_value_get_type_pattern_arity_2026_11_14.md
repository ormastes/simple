# Runtime Value.get_type aggregate pattern arity

The provisional Phase 3 build at frozen `7a35581a21a53` completed its 1,665-module
HIR collection but failed on `compiler.common.runtime_value_v1`. Its `get_type`
matched `Struct(_)` and `Enum(_)`, although the real declaration has respectively
two and three payload fields. The fix supplies the missing wildcards, preserving
existing `Opaque("struct")` and `Opaque("enum")` results and normal arity checking.

Focused native regression: **PASS**. Full imports, core/MCP smoke, and bootstrap
phase qualification: **UNRUN**, delegated to the bootstrap owner after landing.
No claim of Phase 3 admission or broad production readiness is made.

`runtime-value-get-type-projection.py` copies the actual recursive 125-declaration
Value/HIR/MIR closure and unchanged get_type/MirType factories. Every copied
record has an owner and SHA-256 in retained provenance. It strips imports only
for this scoped projection; the real-import companion spec remains unexecuted.
No payload record is mocked and no checker exception is enabled.

The exact producer SHA-256 is
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
Native builds use `--threads 1 --runtime-bundle core-c`, an explicit private
`--cache-dir`, and, for the final controlled pair, private `XDG_CACHE_HOME`.
The launcher samples process-group RSS every 0.2 seconds, terminating at 2 GiB
or 120 seconds; no address-space limit is applied. RSS is a sampled measurement.
Exact producer path, argv, exits, timings, and logs are retained under
[evidence](evidence/runtime_value_get_type_2026_11_14/).

Old get_type fails with both expected HIR arity errors. Corrected get_type
builds in 5.690 seconds, sampled peak tree RSS 77,549,568 bytes, then its native
executable prints PASS and exits zero. Assertions cover empty/populated structs,
absent/tuple/record enum payloads, integer and nil results, and wrong-kind
negative controls. Changing only the two source patterns separates the final
controlled pair.

An initial corrected-source harness attempt reached MIR and exposed the already
tracked inline-empty-dictionary bug
`mir_enum_payload_inline_dict_literal_key_annotation_mismatch_2026-11-14`.
The control now uses a typed local dictionary. That failed attempt is retained;
it is not evidence against the arity repair. The final old-source control uses
the same typed harness. The first control's HIR cache was project-namespaced in
the host cache despite its private object cache; the final pair also isolates
XDG cache storage.

Reproduce fixture generation with Python 3 using `--repo <checkout> --output
<new-private-dir>`; add `--value-source <original-runtime_value_v1.spl>` for the
old-source control. Initialize and commit the generated fixture to a private Git
repository, then invoke the retained native-build command from that directory.
The parser/record closure is a test projection, not an import-surface substitute.
