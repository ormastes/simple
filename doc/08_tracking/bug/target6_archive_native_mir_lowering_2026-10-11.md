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

## Focused repair result (2026-10-11)

Canonical identity sorting, explicit borrowed-owner array reads, direct
dependency appends, and Result variant branches removed the initial
sorted/contains/concat/unwrap MIR diagnostics in this closure. The first
retry stopped at workaround annotation placement; that marker now directly
precedes its affected function. The final bounded retry completed HIR
69/69 and reduced 45 emitted MIR errors to 6 repeated errors at only two
source locations: interface_action_archive.spl lines 219 and 221. Both
iterate arrays obtained from Result Ok payloads; this Stage 2 MIR sees
their collection type as I64 and refuses for-in. No native executable
was produced. Log: build/mini_builds/item6_archive_grouped_publish_mir_final.log.

The three-cycle cap is exhausted for this feature in this session. Next
work should preserve payload validation and use an explicitly indexed
array shape at those two loops, then rerun the focused native fixture
before any performance or release claim.

## Indexed-loop candidate

The two `for-in` loops now use explicit indexes over the decoded symbol and
action arrays. This preserves the duplicate-symbol and target-membership
validation while avoiding the two MIR sites reported in the final log. This is
source-only progress under the session's three-cycle cap: the candidate has
not been rebuilt or run, and the native/runtime verdict remains open.
