# Result dictionary payload unwrap rejects a declared module index

Status: production fix and regressions authored; compiler/runtime UNRUN.
Requirement: REQ-ENUM-RESULT-DICT in the robust enum hardening plan.
Base: `2f7439a9cebafe4fd34bd9743720e01faed2da5b` (coherence PR 3776 merged).

Concrete receiver witness within historical group 104:
`ModuleSurfaceBuilder.add_indexed_name` calls `module_surfaces_add_name`, whose
current signature is `Result<Dict<text, i64>, text>`, handles Err, then assigns
`name_result.unwrap()` to `index_by_name`. The actual unwrap implementation
`lower_result_unwrap_core` admitted Array payloads but not Dict. Its fallback
emitted fatal `unsupported Result unwrap payload type` for this declared
receiver. This establishes a concrete source failure, not an attribution of
every historical module-summary diagnostic to this one call.

The repair admits Dict only when no default expression is supplied. It uses
the existing declared `lower_type` mapping, copies the raw `rt_enum_payload`
handle into the typed Dict local, retains the exact HIR payload, and records
dictionary/tagged-value/value-type provenance for normal downstream dictionary
read decoding. It neither allocates nor clones a dictionary, reboxes its word,
or decodes that handle as an integer. Nominal record fields remain owned by the
declared dictionary value type and existing shared dictionary-reader logic.

The same helper's no-default mismatch previously called `rt_panic`, assigned a
zero result, and jumped to merge. It now terminates Abort after the panic call.
The exact tag comparison accepts only Ok tag 0 or Err tag 1 as requested; any
other tag takes that divergent mismatch path. A returning panic cannot produce
a fabricated payload. Supported scalar defaults retain their fallback/merge
path. Default-bearing dictionary unwrap/projection and unsupported Optional
payloads still reject with their existing fatal diagnostics.

Backend source inspection: `MirBuilder.terminate_abort` installs Abort;
LLVM `core_codegen` emits `emit_panic_trap_ir`; both Cranelift routes emit trap
code 1, and native target selectors already support Abort traps. No owned
pure-Simple C emitter was identified by the bounded search, so C bootstrap
emission is unqualified. No backend, runtime ABI, or seed implementation was
changed or executed.

Regressions use the existing SSpec runner:

- `result_dictionary_unwrap_runtime_spec.spl`: six actual-value scenarios for
  receiver-once, unwrap_err, floating/text values, empty dictionaries, nominal
  record field ownership, and the actual module-name builder's success,
  idempotence, and precise conflict behavior.
- `result_dictionary_unwrap_lowering_spec.spl`: four production MIR probes
  for exact independently expected Dict types, raw payload copy, retained
  metadata, exactly the three expected runtime calls, both tags/Abort edges,
  unsupported/default-bearing rejection, and preserved scalar-default merge.

The MIR call-count oracle excludes collection allocation/clone calls on the
unwrap path. It is source-structure evidence, not measured allocator/RSS or
timing qualification. Production adds only local type lowering and existing
local-provenance bookkeeping; no module scan, collection traversal or cache
change is introduced. Native performance remains UNRUN.

All ten scenarios are authored, none executed. Historical group 104 receives
a concrete receiver repair, not a blanket closure. Other Result receiver
groups 111/116/117/120 and group 108 constructor attribution remain open. No
general enum completion, formal proof, or release PASS is claimed. Root owns
the existing six-total retry accounting, independent review, and landing.
