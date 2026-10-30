# MIR prescan copies complete HIR registries for duplicate names

Date: 2026-10-26. Status: first no-copy candidate rejected by native scope test;
revised ownership candidate source-reviewed but not natively qualified.
Prepared for landing under the user's explicit unverified-source authorization;
this does not qualify the rejected candidate or claim a native PASS.
Canonical bug-database reconciliation is pending; the qualified writer is not
available in this bootstrap environment.
Related underlying bug identity:
`native_boxed_dictionary_key_journal_identity_2026_10_26`.

## Observed owner

The Phase 3 diagnostic build used the immutable pure-Simple Stage 2 compiler
`acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`
(source `f9d07913dcc`). Its HIR phase completed 1518/1518 modules successfully.
Two brief LLDB samples of PID 31816 showed progression from
`MonomorphizationPass.named_type_name_in` to MIR prescan:

`rt_dict_set -> bootstrap_fn_ret_hir_type_register +696 ->
MirLowering.prescan_one_function_v1 -> prescan_module_functions_v1 ->
prescan_module_struct_names -> CompilerDriver.lower_to_mir_with_target_context`.

Offline disassembly places offset +696 inside the loop that copies every
other return-registry entry after a duplicate name. This establishes a hot
prescan owner, not an infinite loop or a failure of object emission. The live
build subsequently reached object generation. Both debugger samples detached
successfully; the live process, compiler binary, runtime authority, and caches
were preserved.

Evidence is retained under
`C:/dev/wt-bisect/build/native_probe/phase3_optional_payload_subst/stage2-acfedbebd1db/`:
`phase3-main-stack-01.txt`, `phase3-main-stack-02.txt`, and
`phase3-register-offline-disassembly.txt`.

## Rejected candidate and ownership finding

Both return and parameter HIR lookups already veto names in
`_bootstrap_fn_ret_hir_ambig` before reading their metadata. Registering a
duplicate in the candidate retains the hidden old row instead of copying the whole return
dictionary and then the whole parameter dictionary to delete that row.
Duplicate names, including equal-signature declarations, remain ambiguous.
Symbol-bound metadata rejection and parameter rejection remain unchanged.

Source-level insertion journals each key and HIR value/list, but that is not
proof of native object identity. Disassembly of the candidate shows that
return registration calls `rt_string_new` at offset +410, then `rt_dict_set`
at +427. `_bootstrap_fn_delta_text` independently calls `rt_string_new` at
+50 before `rt_array_push` at +61. The text journal therefore contains a
different boxed string from the dictionary's stored key. The candidate's
later-scope ambiguity veto did not survive cleanup: both lookups returned
`Some` for `registry.native.scoped.0`. A debugger confirmed the exact key and
loop index, ruling out a loop-variable or key-formatting mistake.

No whole-map-copy removal can be accepted on the assumption that the text
journal owns the stored native key. Actual dictionary-key ownership must be
preserved first, or a narrower optimization must retain the original scoped
behavior. The independent boxes are recorded in
`candidate-register-journal-disassembly.txt`; the failing lookup is captured
in `candidate-scope-failure-debug-03.txt`. Debugger children were terminated
after inspection; the main build was not attached during this diagnosis.

The first wholesale-adoption diagnostic now counts hidden retained rows too.
That count describes stored roots, not callable names. Retained memory is
bounded by one old return row and one old parameter row per distinct name;
later duplicate registrations cannot add more rows. No public data layout,
ABI, runtime source, or Stage 2 binary changes are required.

The existing `Dict.remove` interpreter/native return-value discrepancy is not
used or changed. The separate named-type suffix-index optimization is tracked
by PR #4856 and is not duplicated here.

## Qualification

The native fixture imports the production registry owners:
`test/fixtures/compiler/registry_ambiguity_no_copy/main.spl`.
The pre-change baseline compiled its 140-module closure using the admitted
Stage 2, LLVM GNU Windows target, and `core-c-bootstrap`; it returned 0 after
checking 256 duplicate names, repeated registration, an unrelated keeper, and
equal-signature ambiguity. Baseline executable SHA-256:
`8a07ee00c257d86bb36aa9d5777ddb063ab3552aa883a91d82d8324e20193714`.
Its immutable SCV revision is
`299ef44b9ea70f11383f3ad72a10e80f71ccb91ff9bfe417ea7436b14002ac98`;
the baseline fixture and registry source remain in that snapshot.

The candidate adds native scope checks for insertion-scope and later-scope
ambiguity, metadata survival after cleanup, and promotion-root counts of 1
for a new ambiguity and 0 for its repeated registration. The executable SSpec
`test/01_unit/compiler/mir/bootstrap_fn_registry_delta_promote_spec.spl`
also covers the intended bounded promotion behavior, but is unrun. The
candidate compiled and linked successfully, then failed its scope check with
exit 25. Candidate SHA-256:
`19931e8a8f38430b15c290cbb05ea0c0bd0457c902ac6f56cc39f55d871c4640`.
The candidate SCV revision is
`3d4870d5ebf9ac879e66e759066b50f15733ae352a365fc4c3e9e10a5b0ad844`.
The extra transient-scope import expands the candidate closure to 141 modules.

A control restored the production registry source to SHA-256
`79b38fe5e3750e2d651291581e1f57a1f1069785ed4bf92d820b26636610abe3`
and retained every scope semantic check. The performance-count assertions
were moved after the semantic checks to distinguish the two failure classes.
The first control admission refused a stale source inventory with
`SCV-E-ADMISSION: snapshot-index-drift`; the supported
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` refresh retained all caches and snapshots.
The admitted control then compiled and linked its 141 modules, passed every
scope semantic check, and exited 24 only at the proposed performance-count
assertion: the original implementation promoted 127 roots, rather than 1.
Control SHA-256:
`465960a9af8690c1d4a1165d6bb874c9b5739755d2827b6f17d24ddd4740985a`.
This establishes a scoped semantic regression in the proposed optimization;
the source was restored and no PR was opened. The candidate source patch is
retained as `candidate-source.patch` beside its immutable SCV snapshot.

## Revised candidate, pending native qualification

The revised source still removes both HIR metadata dictionary rebuilds. A new
ambiguity registration marks the actual ambiguity dictionary dirty when a
transient scope is active. Promotion walks that dictionary before scope end,
so its stored boxed keys are retained. The independently boxed text journal is
not used for ambiguity keys. Existing ambiguity registrations return without
rewriting or promoting their keys. First-use adoption already covers the whole
dictionary; delta reset clears the dirty marker along with other scope state.

This is a correctness workaround for native boxing identity, not constant-work
promotion: a new scoped ambiguity still visits the ambiguity dictionary. The
revised test reports the actual promoted-root counts and verifies that adding
64 unrelated return/parameter records does not increase the next ambiguity's
promotion cost beyond its one new ambiguity row. It preserves every semantic
scope check, including same-scope insertion and repeated registration, and
still requires zero roots for a repeated ambiguity. No native build of this
revision has been launched while Phase 3 recovery and the Phase 2 refresh have
priority. Earlier failure/control executables and snapshots remain immutable.
Remove the whole-ambiguity-dictionary promotion only when the native compiler
and journal preserve the identity of the stored boxed key and the same scope
checks pass with key-only promotion. Do not substitute promotion of an equal
but independently allocated text value. The original production source and
the failing first candidate provide rollback and reproduction references.

Native probe evidence is retained under
`C:/dev/wt-bisect-good/build/native_probe/registry_ambiguity_no_copy/stage2-acfedbebd1db/`.
The baseline correctness run took 160 ms including process launch; this is not
a throughput benchmark, and the candidate performs additional scope checks.
No whole-compiler speedup or complete SPipe/core/MCP PASS is claimed. The
available Stage 2 is a compiler-only diagnostic producer, not the full test
runner. Source checks, native qualification, and remaining gates must be
reported separately.
The working-tree direct-env runtime guard passed, `git diff --check` passed,
and the generated-spec tree contains zero executable `*_spec.spl` files.
