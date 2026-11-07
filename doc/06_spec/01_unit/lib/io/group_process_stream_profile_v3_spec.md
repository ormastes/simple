# Group stream CPU profile V3 manual

Planning capability follow-up: `linux_process_stream_template_admit_v3` in
`std.nogc_sync_mut.io.linux_process_owner` validates the canonical V3 template
and invokes the same native target check as launch admission. It creates no
ticket, claim, reservation or helper and accepts zero planning expiry without
fabricating a grant. Success is a current observation, not readiness or future
launch authority. The actual launch path still validates a positive deadline.
Two added cases in `piped_process_profile_v3_spec.spl` reject missing V3 policy
and exercise native refusal of a non-cgroup target with zero planning expiry.
Both follow-up cases are NOT_RUN; the prior native evidence did not test this
new Simple wrapper. There is no new native ABI or duplicate provider.

Status: native typed-policy/readback-parser contract PASS only; 9 SSpec cases
NOT_RUN / AWAITING_VERIFICATION. Source review is not execution evidence.

Executable: `test/01_unit/lib/io/group_process_stream_profile_v3_spec.spl`.
The six cases derive exact quotas at 1/9/10/25/1000 millicores; reject invalid or
overflowing CPU, inconsistent redundant quotas, broker CPU/memory overruns,
unknown image modes and relative broker paths; roundtrip canonical profile bytes;
bound a percent-heavy receipt; isolate strict V2/V3 and reject monitor with a
profile; normalize only grant deadline/transport in templates; reject template
launch and permit pre-grant profile attachment without fake expiry.

`test/01_unit/lib/io/piped_process_profile_v3_spec.spl` separately covers full-owner
transfer provenance and final-owner/pre-grant template correlation (parent lane).

Native contract: `src/runtime/test/group_stream_profile_v3_selfcheck.c` exercises
exact typed 12-word validation, no unlimited/fallback mode, no-effect admission
refusal and exact cpu.max parsing with normal CoreC providers. Its temporary
regular file is a parser fixture, never kernel enforcement evidence. Run only
once after an allocated new build; CPU affinity is 0-4 and runtime alarm 10s.

Positive qualification still requires an actual delegated cgroup-v2 parent with
cpu+memory, a separately budgeted sibling broker scope and protected identity.
Verify actual broker placement/inode/cap readback, helper cpu.max before clone,
readback mismatch refusal, cpu.stat throttling including descendants, deadline
pre-exec rejection, trusted original dynamic image and no silent fallback.
Missing delegation is a rejection, not a passing enforcement test. Neither these
pure specs nor the negative native fixture qualifies dynamic Podman execution or
complete broker recovery. Existing durable owner/cleanup evidence is preserved.

Failure-path acceptance (NOT_RUN): after admitting a real child, make
`broker.resources.sdn` unpublishable (for example, a directory at that exact
protected fixture path). Verify the initial publication returns in one attempt,
no Ready receipt appears, the real lease still processes cancel/timeout and
collects its tree, and no terminal receipt escapes before resources are durable.
Remove only the fixture-owned obstruction; verify the retained admitted profile
is published and then the real collected terminal proof becomes available.
No-child admission must publish only its distinct unlaunched proof and must not
claim a resource-enforced child. This needs an actual supported cgroup fixture;
pure text matching or synthetic success flags are insufficient evidence.

Allocated native contract evidence: one normal-CoreC build and one bounded run
exited 0. See `group_stream_profile_v3_native_contract_evidence.sdn` for exact
source snapshot, command and binary hashes. This narrow PASS is limited to typed
policy rejection and exact readback parsing. Pure SSpec, actual cgroup CPU
throttling, broker placement, dynamic-image launch and full recovery remain
NOT_RUN.

The recorded runtime_process.c hash is boundary provenance only, not a linked
translation unit in this recipe. This is not a complete system dependency
manifest. Separate build/run timing is unavailable; no timing is inferred from
the command timeout limits.
