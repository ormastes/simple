# Cranelift stored text, runtime handles and imported globals

Status: provider and canonical receiver checks PASS; focused native behavior FAIL; full-host qualification blocked by HIR memory cap.

The stage2 receiver built by producer `48a67ecf` completed MIR verification and emitted seven modules, then failed four Cranelift modules. `static_probe` rejected runtime-initialized `_mcdc_static_registry`; `aspect_readiness` and `facet_registry` rejected immutable text literals `READINESS_READY` and `FACET_PRESENT`; `dynamic_aspect` rejected imported `READINESS_FULL`. These are three storage capabilities, not malformed enum constants. Evidence: `.simple/storage/build/phase3-producer-refresh-parse-ownerfix-20261015/retained-receiver-aot-failure-cycle3/`.

Upstream PR3472 already routes mutable text literals through guarded runtime initialization. It does not cover stored immutable literals, runtime aggregate handles, or external data declarations. The follow-up extends that owner rather than duplicating the upstream change.

Stored immutable text now uses the existing ordered, guarded module initializer so storage receives a boxed runtime string. Private immutable literals retain the constant path. Cranelift accepts uninitialized runtime-handle slots using its existing pointer representation; constant aggregate payloads remain rejected. External declarations use linkage 1 through the existing seven-argument global-data provider ABI. The provider declares the symbol without defining bytes and rejects nonzero initial bits for imports, preserving a single defining owner and the existing target scalar/alignment checks.

Regression artifacts:

- `src/compiler_rust/compiler/tests/cranelift_imported_global_data.rs` directly verifies actual provider object symbols, initialized owner bytes, alignment and consumer relocation with no duplicate definition; it does not invoke the seed interpreter.
- `test/fixtures/compiler/cranelift_module_statics/main.spl` and `owner.spl` form a native cross-module execution regression for immutable text, mutable imported scalar identity, runtime aggregate replacement and array initialization/mutation.

The rebuilt provider AOT test passed once (1 passed, 0 failed). The matching pure producer and runtime compiled all four formerly failing receiver modules; both canonical receiver programs compiled, linked and ran successfully. `four-module-object-proof.json` and `final-receiver-object-proof.json` retain source, capsule, object, actual link and relocation evidence. These are Cranelift results; the earlier LLVM receiver result remains separate.

The focused fixture first failed before parsing because the direct positional collector excludes `/test/`. A second, independently reviewed attempt used byte-identical immutable copies in a private `/tmp` package, retaining the original-to-copy hashes and using a separate cache. All 12 modules compiled and linked, but the generated executable crashed with SIGSEGV before its PASS output. Object evidence proves one defining module for `LABEL` and `counter`, with undefined importer symbols and actual relocations; it does not prove the runtime value or positive recording assertions. The remaining failure is documented in `mcdc_token_stack_alias.md`. This relocated attempt does not qualify the original `/test/` collection route.

The final canonical matrix parsed all 2,679 files and completed surface construction, then reached the 8 GiB cap at HIR 836/2,679 (exit 88; observed peak 8,449,128 KiB). The full test host is not qualified. Authored SSpec, docgen and required broad core checks remain UNRUN; no seed interpreter substitutes for them. Evidence is retained under `.simple/storage/build/phase3-cranelift-static-provider-20261015/`, including `provider-object-test-cycle2.env`, `module-statics-native-proof-copied-source/result.json`, its `object-proof.json`, and the canonical matrix receipts.

The matching native regression also checks instrumented module initialization: a module-global atomic must initialize to 23, and MC/DC must record decisions after configuration. This covers the subsequent startup failure documented in `mcdc_probe_bootstrap_initialization.md`; it does not replace the static-data object/relocation or native value assertions.
