# Archive/CAS native MIR lowering blocks focused Item 6 probe

Status: OPEN (2026-10-11). A no-stub pure-Simple Stage 2 native build
of test/02_integration/compiler/cas_batch_native_publish_main.spl
completes HIR for 69 modules but fails MIR; no executable is produced.

The first real diagnostics occur in src/compiler/80.driver/cache/
package_archive_cache.spl around Result tuple extraction and array concat.
Further sites in cas_batch_transaction.spl use sorted over an array;
interface_action_archive.spl uses contains, collection for-in, and Result
payload extraction. The log emits 45 errors across repeated MIR passes.
One archive concat was replaced with an array append loop in the candidate;
the remaining errors still require compiler/language-surface repair or
equivalent source changes with preserved semantics.

Reproduction log: build/mini_builds/item6_archive_grouped_publish_native.log.
Expected: MIR lowers the same typed HIR without placeholder method calls,
the native fixture links, and its multi-package SCC publish/load assertions
pass. Do not infer a runtime or performance PASS from HIR completion.
