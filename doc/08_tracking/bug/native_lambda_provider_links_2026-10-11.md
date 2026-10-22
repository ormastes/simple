# Lifted lambdas lose imported callable linkage

Native producer54f23cb2 (source6bffb3135df, strict sanity PASS) reproduces this
with two source modules. Provider exports imported_value()->7 and invoke(callback).
The flat consumer invokes a callback that calls imported_value. Its AOT succeeds,
but linking fails: nm shows an undefined bare `imported_value`, while the provider
object defines `app.native_provider_link_diag.provider.imported_value`.
The nested consumer returns an outer lambda calling invoke with that same inner
callback. LLVM AOT rejects `call i64 @invoke(void %l1)` and MIR reports unsupported
lambda conversion. Genuine std.spec likewise produces `call void @it(ptr, void)`.
Evidence and exact sources: permanent-repair/normal-firstfile-cycle3/provider-link-repro
under /home/yoon/dev/phase2-six-results-20261011.

`lower_lambda_value` creates a fresh MirLowering and copies provider ABI metadata,
but omitted callable_link_names. Both provider_callable_has_link (capture analysis)
and provider_callable_symbol_name (relocation) need that registry. The repair copies
the existing map beside callable_text_value_abi. It changes no name lookup or symbol
selection rule. is_known_top_level_function still checks the declaration's actual
kind before provider lookup, so a local symbol stays local. Capture and parameter
bindings still use the existing fresh lowering's bind_local paths.

The native fixture covers aliased imported function calls in flat/nested callbacks,
a local callable shadowing the imported alias, and a captured integer shadowing the
same alias. Expected values are7,7,11,13, with distinct nonzero exits on failure.
Runtime verification of this repair remains PENDING in the next owning compiler
lane. No fourth compiler build was launched in the bounded repair session. The
normal std.spec workaround must remain until original and negative tests execute.
