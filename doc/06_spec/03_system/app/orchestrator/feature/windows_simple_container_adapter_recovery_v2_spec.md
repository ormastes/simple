# Windows common API recovery-only candidate regression

Requirements: REQ-WDP-007, REQ-WDP-010. Status: **AUTHORED_NOT_RUN**.
No compiler, build, test, native capture or Docker command was executed.

The executable scenario uses the actual Windows scripted provider, actual
Windows adapter and portable Simple Container API. An explicit test-only wrapper
constructs a scripted service owner. Native and finite production factories never
select this path. Initial successful inventory is mandatory, with a maximum of
16 scripted inventory batches and 64 entries per batch. Fixture observations
carry an explicit fixture-only policy/scope/provider pin and never claim native
Windows identity or host journal durability. Startup is always quarantined.

The scenario returns a valid native create ID and fails the following engine
confirmation. The returned common owner retains the same candidate in intent,
with recovery-only rights. Wrong native-ID recovery, start, stop, destroy and
ordinary reads fail before any additional provider command. Exact recovery
queries the matching engine, image and complete scoped native object and then
promotes ordinary lifecycle rights. A refused duplicate create preserves those
full active rights, with no second native create. Start, stop and exact destroy
then succeed through their scripted real-owner paths. A refused create after
destroy cannot revive retired authority or permit recovery.

The scripted command cursor assertions distinguish actual command consumption
from static returned values: 6 after failed confirmation, unchanged through
wrong-ID/candidate-only refusals, 9 after exact recovery, unchanged after duplicate
create, 14 after start and 24 after stop/destroy/positive absence. The script
contains exactly one native create result. These are authored assertions, not
observed pass counts or native lifecycle qualification.

Dependencies: the integrated common execution/service API and the Windows
wrapper in test/fixtures/container/simple_container_api_fixture_v2.spl, owned by
the orchestrator lane. Fixture helper:
`test/fixtures/orchestration/simple_container_windows_adapter_fixture_v2.spl`.
Specification:
`test/03_system/app/orchestrator/feature/windows_simple_container_adapter_recovery_v2_spec.spl`.


Additional authored startup scenarios reject native providers in the explicit
fixture factory, mismatched fixture pins/timeouts and absent/failed initial
samples. Common service refresh consumes the next actual scripted batch, keeps
old-scope resources charged, rejects stale inventory admission and requires a
commit correlation for nonempty inventory. Refresh error/exhaustion returns no
inventory and invalidates the previous admission digest; no cached empty/success
fallback exists. Startup refresh is unavailable after publication.

**Typed admission values, synthetic revisions and fixture commit digests are
contract inputs only. They provide no evidence of actual durable host journal
commits or retained startup receipts.** The host lane separately verifies the
real journal/startup-receipt owner. These scenarios prove nothing about native
Windows inventory or persistence until actually executed with the real owners.

All source scenarios remain AUTHORED_NOT_RUN. No new pass count or native
qualification is claimed.

The adapter also refuses admission based only on factory inventory. A successful
explicit startup refresh is required before acknowledgment; a failed refresh
invalidates that readiness and any prior cached digest. The host remains
responsible for holding the real journal writer across refresh and handoff.
