# Same-account expression codec prerequisite

Status: implementation checkpoint2 for independent source review. No source
invocation or driver activation is claimed. Root owns integration; compiler,
native and SSpec execution remain UNRUN.

`FlatPoolReader.new_accounted_v1(blob, max_input_bytes, max_allocation_bytes,
max_nodes, max_depth, max_work_units, account)` and
`HirCodecWriter.create_accounted_v1(max_output_bytes, max_allocation_bytes,
max_work_units, account)` return Result. They prepay cursor/empty-array retention
before construction and install the supplied account inside the shared
constructor before its first scan. Ordinary constructors delegate with nil;
their grammar, local guards and legacy audit-event order remain unchanged.

Existing `charge_work` and `reserve` seams debit the actual live account before
advancing counters and before guarded scan/split/growth. Refusal poisons the
codec. No account is created, refunded, reset or replaced with a copy of its
remaining capacity. `mir_loop_codec_charge_v1` uses named reserve arguments:
work is exact requested work plus twice allocation; state_fields and output_bytes
each receive allocation. Product/sum overflow fails before debit. One retained
state field per allocation byte is a conservative logical allowance, not a
native representation assertion. Structural caps remain independent guards,
not a prepaid maximum-size artifact envelope.

`mir_hir_expression_from_retained_blob_v1(record, authority, final_key,
body_digest, blob, account)` has no filesystem context or loader fallback. It
pays metadata comparisons/key encoding and SHA work before processing, validates
bytes against the record, then uses a fresh accounted reader and writer. The
ordinary loader and this consumer share decode/stable-reencode logic. Key and
expression encoding use the same existing byte grammar under optional account
hooks. Fixed cursor retention, actual text bounds, prefix/digest storage and
final output equality are prepaid. No partial decoded result is returned on
failure. The supplied record and hash remain comparison data; the private owner
must independently bind them to the current admitted repository.

Generated encoding previously continued walking children after a writer charge
failed. The source generator now emits account-aware entry/depth guards before
heap checks, charged loop guards before traversal and each iteration, and an
immediate account-aware poison check after writer/child calls. The checked-in
artifact was mechanically updated by the same rule without running a compiler.
Nil-account traversal retains its prior failure behavior. Paid visit counts and
depth unwinding make refusal observable independently of the final error.

A bounded source callgraph walk from `hc_enc_hir_expr` reaches40 generated
encoders and no dictionary `.keys()` snapshot. Shared guard generation covers
other encoders too, but this does not qualify their unmetered dictionary
snapshots; whole-module encoding is outside this expression checkpoint.

The decoder imports no driver or filesystem access. It grants neither archive
admission nor a default-relocation proof. Actual archive target collection/reset,
retention completeness including transitive defaults, and same-account
declaration-link/remap work are required next. The callable replay P1 remains
OPEN until those boundaries and both replay callers are wired. See the linked
[bug](../bug/source_region_field_default_replay_budget_20261026.md).

Twelve meaningful authored UNRUN specs cover exact reader constructor debit1372,
one-short scan refusal with no split debit, failed writer allocation with stable
counters, ordinary/accounted writer byte equality, overflow without debit,
fresh decoding of an actual frontend field default, modified bytes and changed
provider identity. Local artifact fixture records prove codec mechanics only;
they are not fabricated archive admission or an end-to-end positive.
Nested actual frontend trees additionally prove zero visits on entry refusal,
one paid root visit then immediate stop on failed put, funded byte equivalence,
and unwind after the actual account depth limit.

Logical precharge is the scope of this checkpoint. Existing codec allocation
envelopes, physical allocator behavior, runtime performance and complete driver
invocation remain unqualified. No green checks were rerun and no heavy jobs ran.
