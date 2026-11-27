# Proof-only owned pipe retirement V2

Status: source implementation under review; all new tests NOT_RUN. No native ABI,
C owner or policy changes, runtime campaign, broker launch or positive cleanup
qualification are introduced.

`process_retire_piped_owned_v2(owner, reference?) -> Result<(),text>` validates
the original complete owner and optional reference using the same private helper
as cleanup, reads the canonical cleanup proof once, and returns its error
immediately if absent/malformed. It never publishes cancellation or retries the
proof read. With actual proof, a shared private helper invokes the unchanged
native exact-generation/root/identity retirement. Nil recovery still accepts
native stale only after real proof; Some(ref) retains stale-reference error.
Durable owner/audit files remain available. Failure retains caller-owned values.

`process_cleanup_piped_owned_v2` keeps its prior semantics: shared validation,
proof read, then on failure bounded cancel and proof reread, then the same private
retirement helper. Proof-only settlement now imports/calls retire(native,nil)
in host_helper_settlement_v1; ACK/schema and journal sequencing are unchanged.
Other Container/SOSIX consumer adaptations remain their owners' separate scope.

The existing owned-pipe unit spec adds owner-tamper/ref-mismatch negatives and a
real0700 temporary-root fixture prepared through the canonical immutable request
metadata writer. Missing proof then malformed no-child proof must return Err
without creating broker.control.request; canonical claim/request bytes and owner
identity must remain unchanged. These metadata files do not fabricate native
launch authority, an admitted broker or terminal success. No positive retirement
is asserted. Existing Caret live-process helper is untouched. All cases remain
NOT_RUN until an independently allocated producer executes them.
