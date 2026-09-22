# Cranelift qualified calls disagree with bare definitions

Status: root cause CONFIRMED; focused native naming red/green and nineteen
contracts PASS after separately qualified provider repair. Independent Astra
review PASS approves the focused naming commit.
No full compiler rebuild, bootstrap, general test-suite, or push claim.
Baseline: `b9107f6d218f7e2e5d20be152744b8604c536781`.

## Actual compiler-path red evidence

Frozen candidate SHA256:
`bf1951bd045d89481a85430b9e648e42846e3dc4c92f147ecc8f90f19c712b58`.
Evidence root:
`/Users/ormastes/simple-tmp/stage2-result-identity-20260923/build/native_probe/result-identity`.
Both failure.log and original-cwd.log complete two-module object generation,
then fail to link compiler.common.module_path_naming.module_logical_name_from_path.
The candidate's objects under original-cwd-cache/darwin_link_inputs show bare
definitions `_module_logical_name_from_path` and
`__module_path_naming_strip_numbered_dirs`, but qualified imports from both
the caller and module-internal helper calls. No object defines those qualified
names. This is independent of the original unreproduced capsule rejection.

The Cranelift adapter's declaration and body naming only receive func.name.
MIR call operands already contain module-qualified symbols. The LLVM adapter
has a non-entry definition qualification policy that Cranelift lacked.

## Proposed correction and review adjustments

The working Cranelift patch resolves one name policy for declaration and body,
registers both local/bare and emitted names in the handle map, and does not
mutate the frozen MIR graph. Entry identity uses the canonical
module_logical_name_from_path and SIMPLE_NATIVE_BUILD_ENTRY policy (absent
entry means true), rather than inferring entry status from main presence.

Naming priority: entry/non-entry main, explicit export_name, is_global,
no-mangle, existing runtime-owned local symbol policy, then ordinary bare
non-entry module qualification. Already dotted names remain unchanged.
Independent Astra preliminary review caught missing export/global priority
and incorrect main-presence entry inference; both were corrected before any
native attempt. Final runtime acceptance remains unavailable.

The patch adds one additional dictionary alias per ordinary qualified function,
with O(function count) space, and no new full-module scan. Entry/no-mangle env
values are read once per module instead of once per function. No production
performance claim is established; emitted name concatenation is linear in
symbol length. Source contract assertion was updated but not executed.

## Historical projection qualification failure

Fixtures: test/fixtures/native/cranelift_module_symbols.
Evidence: build/native_probe/module-symbols/{red,green} in the same worktree.
The fixture extracts the exact old/new production name-selection functions
and uses real Cranelift wrapper calls to emit/link two same-leaf modules.

Cycle1: both builds exit0; both runs exit134 in the named runtime trap
rt_cranelift_new_aot_module_triple, before emitting any object.
Cycle2: explicit dynamic-runtime bundle builds exit1 because the frozen
producer permits that lane only for the actual Stage4 entry. No bypass used.
Cycle3: core-C bundle plus SIMPLE_LINK_OBJECTS pointing to the frozen
libsimple_compiler_backfill.a again builds successfully, but both runs exit134
at the same trap. The frozen producer did not produce a probe linked to the
real compiler provider. The exact cause of this provider selection is not
diagnosed here. No generated unresolved stubs are accepted as implementation.

Final red/green probe hashes:
`82a2e6e014b413efa9fa83f303a85ff9af1f6c006bb4f0df1434c0ec7697c467`,
`e30be656db28208a202302c0beac0d4b0a97c755406579dbce23a1c99ca66156`.
Third builds took2.27/2.32s; peak sampled process-tree RSS193392/188464 KiB.
All ten build/run receipts show zero observer errors and quiescent cleanup.
All are below5859375 KiB sampled cap; there is no kernel hard limit.
These measure failed probe setup, not passing codegen performance.

The nineteen naming contracts have not been built or run. Neither have the
intended native object link/run or a full adapter/MIR path. No acceptance
criterion is marked green based on helper source inspection alone.
The three-cycle guard ends this lane. Preserve the patch and caches, then
qualify a real compiler-provider probe environment in a separately scoped task
before accepting or committing the production change.

Historical independent Astra review: static naming PASS, runtime BLOCKED, no commit
approval. Review confirmed both corrected policy gaps and all retained failure
receipts. An existing separate limitation remains: build_signature still forces
functions named main to the i64 return ABI, including library mains. This patch
does not establish complete LLVM ABI parity.

## Provider unblocked and native verification completed

The prior three naming cycles above remain historical failed provider setups;
none were repeated. A separate provider task diagnosed the actual link order:
SIMPLE_LINK_OBJECTS was honored, but the generated core archive force-loaded
strong Cranelift bridge-trap definitions before lazy real-backfill extraction.
The canonical core-C capsule excludes that member. Its mandatory guard-page
selfcheck initially failed on 16 KiB macOS pages; independently reviewed
runtime repair `cd0f23020d1acfc1187657fb6574da6777c7ebd3` resolved that blocker.

New clean worktree: `/Users/ormastes/simple-tmp/cranelift-provider-naming-20260923`.
It includes that runtime repair, whose canonical capsule manifest passes all65
checks. The existing producer remains bootstrap-only; no seed test/SPipe use.
Exact producer SHA256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Canonical archive SHA256:
`7496e6c5e8dbfd769b1bab6c23078928f744dadd923069fa6cd80620fca2d998`.
Compiler-backfill SHA256:
`48d74e7cb822369c978ddf231e75355daad7163a4d1df8aa28a1c0bbf4f59283`.

The documented --emit-archive/external-link path first passed a minimal real
Cranelift create/dispose smoke. Link map proves both provider symbols belong
to compiler-backfill object56, with no bridge trap or generated unresolved
stub object. Astra independently reviewed this provider qualification PASS.
Exact commands and authority paths are in the fixture QUALIFICATION.md.

Native naming evidence under build/native_probe/module-symbols/{red,green}:

- Both extracted production helper ranges are byte-identical to baseline and
  patched adapter source. Modeled MirFunction contains only the three fields
  these helpers consume. Actual Cranelift SFFI emits every native object.
- Both archive builds and object emissions exit0. Red objects define `_value`
  twice while caller imports `_alpha.value`/`_beta.value`; final link fails1
  for both missing names. This is the expected red, not a provider failure.
- Green objects define the two distinct qualified names; caller retains the
  same imports. Link succeeds, executable returns0 (42+99-141). Disassembly
  shows calls to both distinct constant-return bodies and the expected sum.
- Nineteen native naming/entry contracts pass, with the required marker and
  exit0: entry/library main, explicit export, global, no-mangle, runtime local
  aliases, dotted names, empty owner, and canonical entry-path positives and
  negatives. Source-based SSpec remains updated but unexecuted.

Single-run red/green object emission elapsed0.37/0.36s, maximum process RSS
10551296/10665984 bytes. This small114688-byte difference is not a statistically
significant performance claim. Contract execution0.34s, RSS9043968 bytes;
consumer execution0.33s, RSS1376256 bytes. Fifteen fresh watchdog receipts
cover provider and naming qualification: expected red link1, all others0,
zero observer errors, quiescent cleanup, peak sampled tree163136 KiB beneath
the5859375 KiB cap. Sampling is not a kernel hard limit and may miss short
peaks, so /usr/bin/time process maxima are also retained.

Scope limits: this proves the exact name-selection helper plus real native
object/import agreement, not the complete adapter/MIR execution path or Stage2
admission. Both full adapter paths and local-alias lookup are statically
reviewed only; export/global contracts prove symbol selection, not complete
export/global ABI behavior. Original capsule identity rejection remains OPEN.
General compiler/lib/MCP/LSP checks and SSpec remain TEST_BLOCKED
without an admitted general self-hosted runner. No semantic bypass, MIR
mutation, new runtime extern, generated provider stub, or ABI weakening was
introduced. The parent must perform the next canonical Stage2 admission.
