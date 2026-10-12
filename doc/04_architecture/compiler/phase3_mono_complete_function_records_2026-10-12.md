# Complete mono function artifacts

The actual archived-function consumer now publishes a separate immutable complete
function record, in addition to its compatibility complete-module container. The
record uses the actual generated `hc_enc_hir_function`/`hc_dec_hir_function`
codec, including parameter defaults, contracts, effects and the entire body.
No declaration projection or placeholder function is serialized.

The record key binds module, original archive key/body digest, rewritten module
body digest, complete function digest, target name/SymbolId, exact stage and
publication delta digest. The compatibility module key also binds the record
key. Publication application validates both artifacts; a changed record owner
cannot advance the state epoch. `mono_archive_load_function_in_owned_scope_v1`
is the actual borrowed complete-body API for final module assembly.

`hir_owned_artifact_cache_v1` provides borrowed store/load primitives for the
mono records and separately typed MIR expression artifacts. Both require the
actual active/unpaused scope state. Neither starts, pauses, promotes or ends a
scope, nor writes persistent managed diagnostics. The parent owns all returned
objects and must close its own lease after promoting its explicit escape set.

The byte envelope is the existing HIR cache checksum framing plus current
producer header and exact key. Reads reject links/nonregular files and are bounded
to 8 MiB including the envelope. Writes verify a securely staged file, publish
without replacement, then verify the published bytes. An occupied immutable name
with different bytes is refused; an identical concurrent publication is accepted.
This storage primitive establishes integrity, not source/runtime/stage authority.
Callers must retain the complete admitted input identity and typed selector proof.

The function decoder preserves the admitted legacy writer/reader contract. It
requires exact header, full consumption, stable re-encoding and the expected
complete-body digest/name/SymbolId. The separate canonical codec generator is not
admitted and is not substituted. The 8 MiB file bound is not a bound on arbitrary
malformed generated decode allocation; this path accepts producer-framed records
and does not claim a new hostile-byte decoder contract.

The mono native fixture now observes actual values and call names from the
function record and checks its complete digest against the compatibility module
and retained specialization. Seven added controls cover inactive and paused
leases, identical republishing, immutable-byte mismatch with unchanged original,
wrong body digest, wrong name/SymbolId, and publication-owner mismatch without
epoch mutation. The original record patch requires 54 checks. Native compilation/execution
remain pending the root-owned slot; static guards are not native evidence.

This is a prerequisite for final assembly: decode the original complete module
once and only selected complete function records in its owned scope. Decoding a
complete rewritten module container per function would accumulate redundant
provider bodies until scope close. The compatibility containers remain explicit
for current validation and are not the final module stage. Ordered root barrier,
FIFO completion, final assembly and every post-mono validator still need their
actual consumer transactions before production driver activation. No original
promoted HIR reclamation, bounded full route or RSS improvement is claimed.

The shared byte owner and unchanged envelope parser now live in
`compiler.common.cache_contract`, with compatibility delegates under the original
driver paths. There is one storage implementation and one envelope parser. MIR
imports the lower owner with `HirOwnedArtifactContextV1` supplied by the driver's
`hir_owned_artifact_context_v1` factory. The context has directory, producer header
and enabled fields; it grants byte access only. No lower owner imports the driver.
The driver factory preserves the actual current cache selection. Two extra native
guards refuse a changed producer header and disabled context; the updated launcher
requires 56 checks, still unexecuted pending the root-owned slot.
