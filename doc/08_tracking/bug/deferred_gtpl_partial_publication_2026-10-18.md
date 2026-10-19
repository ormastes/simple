# Deferred GTPL section admits an incomplete transaction

Source-confirmed; actual runtime UNRUN. Adjacent workaround:
deferred_optional_tuple_owner_2026_10_11 in deferred.spl. The typed optional
tuple binding preserves template/offset owners, but it does not provide
transactional admission of a complete section.

Before repair, DeferredMonomorphizer.deserialize_templates broke out of the
loop at EOF before the advertised record count, cleared deferred_last_error,
and returned true. It also wrote each decoded template into template_cache
immediately. A valid first record followed by a malformed second record thus
published partial state even when the API returned false, and could overwrite
an earlier admitted definition. These are concrete public API failures.

The producer is compiler.driver.smf_serialization.serialize_templates. It
writes a GTPL version2 header, exact count, and complete records with no trailing
section data. Its historically named serialize_function_placeholder actually
serializes name, generic parameters, parameter annotations, return type, body,
flags and bindings. The regression invokes that owner, not an invented codec.

Repair stages only incoming names/definitions until every advertised record
decodes and the exact section is consumed. Missing records and trailing bytes
return false with explicit errors. Existing decoder failure preserves its error.
On success, existing last-definition-wins duplicate/collision policy applies,
unrelated old rows remain, and deferred_last_error clears. A valid zero-count
header succeeds without mutating old entries. Version2-only refusal and the
typed optional tuple workaround are retained.

Resource scope: temporary staging is O(k) references for k unique incoming
names, not a copy of all N previously cached templates. Publication walks only
the staged delta. This is logical validation atomicity in the existing
single-owner API; it does not add concurrent reader isolation, allocator-failure
rollback, body compilation, specialization-cache invalidation, or typed GTPLv4
admission. Existing per-field binary bounds remain authoritative.

The combined 2026-10-19 port also repairs load_templates_from_smf through
canonical typed-section extraction. It does not claim native loader admission.
Direct transaction tests and real writer/file wrapper tests cover both boundaries.
No gates or runtime guard bypasses are introduced.

Seven transaction cases in deferred_gtpl_transaction_spec.spl cover canonical writer
roundtrip/duplicate replacement, missing advertised record, truncated second
record, actual unknown-kind decoder error, zero-count/trailing controls and
version refusal followed by valid recovery. They assert decoded body/signature
fields and preservation of pre-existing rows. All are UNRUN; RED is predicted
from source. Only the recorded isolated port worktree is changed; donor/build remain unchanged.
