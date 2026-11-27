# Protected profile installation and finite paired cleanup

Source: [host_identity_profile_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/host_identity_profile_v1_spec.spl).
Manually authored companion; **AUTHORED / NOT_RUN**. Existing canonical profile,
reference and generic projection receipt cases are preserved.

The command admits a complete profile or the path-free installer template,
opens one actual retained store, and begins one actual key/pin pair. Acquisition
is bounded to 64 steps. The same paired paths port proves currentness for data
derivation, immediately before immutable publication, and after publication/
existing-byte comparison. The actual protected pin must match its alias, root
and selected auth/trust references. Invalid proof is never replaced by a new
pair or a guessed drive path.

Three additional authored cases use the production turn-policy/receipt helpers:

1. Acquisition advances only for a retained, not-ready pair with no pending
   cleanup or error; missing owners, Ready, cleanup and failure stop it.
2. Close advances only for the explicit normal cleanup-phase marker. Native
   file/root close failures, consumed slots and completed turns never permit a
   retry. The command itself caps cleanup at 64 phases with no sleeps.
3. Confirmed immutable publication, profile reference, file flush and original
   operation error remain present if later pair cleanup is unconfirmed.

On a retained close failure or budget limit the exact parent store, which
canonically retains actual pair children, stays in `host_identity_cleanup`.
The installer does not immediately call parent close and retry that failed
child. Once pair close is confirmed, parent close runs through the existing
owner-bearing path. Locator lookup uses the separate exact `.profile` protected
config accessor; it is never an external SSH path projection. Prior writer
cleanup must complete before the actual loader reacquires the journal.

These source cases do not prove native phase progress, namespace/file
replacement detection, parent drain, durability or a successful loader/SSH
handoff. Service5 Windows and POSIX provider runs remain **NOT_RUN**, including
the lower locator's real loader-forward fixture. No compiler/build/native
campaign was started.

See [template cases](host_identity_profile_template_v2_spec.md),
[setup guide](../../../../07_guide/tooling/orchestration_host_identity.md), and
[remaining storage qualification](../../../../08_tracking/todo/orchestration_host_identity_secure_store.md).
