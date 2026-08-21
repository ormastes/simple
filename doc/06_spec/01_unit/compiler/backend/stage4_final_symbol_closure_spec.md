# Stage4 aggregate final symbol closure

Mirror of `test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl`.

The executable SSpec covers portable provider-leaf matching, hosted archive identity and object ABI, deterministic staging and manifests, strict emit/link behavior, compiler backfill envelopes, localization, disjoint definitions, dynamic-loader provider contracts, and rejection of incomplete, repeated, foreign, or unresolved symbol sets.

Most evidence is static symbol/build-policy validation. It does not replace native linking and execution on all supported object formats.
