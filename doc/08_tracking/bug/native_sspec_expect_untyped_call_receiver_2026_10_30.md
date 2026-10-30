# Native SSpec expect call loses declared return before scalar matcher lookup

Status: actual native failure; separate core repair under investigation. Not fixed by Result-binding candidate `98d0a9ea020`.

The MC/DC-off SSpec entry fails MIR lowering at generated entry line 10:19 on `expect(actual).to_equal(41)`. Log: `/tmp/simple-phase2-runner-native-attempt11-20261030/sspec-mcdc-off/cache/native/diagnostics/native-build-stderr-1061553-2.log`. It reports runtime-fallback, receiver_has_type=false, receiver_type_kind=-1. Producer source was `540671a010a9cc413d8bd2aa464c01e5b02900e9`; target `/tmp/simple-phase2-native-execution-sspec-540671a-20261030`.

Retained entry HIR: cache `235f10985af7c00c3d8935df94c25b472f25fd0748f1537e670178a32091823b.parser-v4.hir` under that attempt's `cache/hir`. Exact generated-codec records show imported Function symbol 42 named expect, owner lib.nogc_sync_mut.spec, with absent optional function type (name at line 1243). The receiver is a direct Call of NamedVar42, with no retained expression type, immediately consumed by to_equal. No intervening binding exists. The imported trait ExpectScalarMatcher is symbol65.

Retained provider HIR is cache `0d36e30d643aa4e9a27131cc35ffa82d1401d8e45d679cce3df5b90cb065ddb0.parser-v4.hir`. Its expect Function symbol106 also has no optional symbol type (name at line5967); the function declaration itself remains present (name at line78895). Both cache-envelope checksums were verified. These are selected record observations against generated codec schema, not whole-module decoder admission.

The source API declares `pub fn expect(value) -> i64`; methods including to_equal are provided by `impl ExpectScalarMatcher for i64`. `declared_imported_surface_callable_type` returns nil when any parameter lacks an annotation, so the unannotated value parameter prevents publishing the otherwise declared i64 return in a complete Function signature. The native entry path cannot then use an attributed receiver to resolve the scalar trait method. This is distinct from Result bindings: candidate98d transports a return already present in an exact Function symbol and only for a local/global binding.

A correct repair must preserve the API's unannotated parameter semantics, retain exact callable/provider identity, and select the actual scalar trait implementation. It must not invent a full authoritative signature, guess Any merely to satisfy lookup, or dispatch by matcher leaf name. Native green and deliberately failing expectations must both execute through the real matcher before this issue is closed.
