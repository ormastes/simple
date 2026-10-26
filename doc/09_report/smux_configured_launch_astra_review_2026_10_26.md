# Configured launch composition: independent Astra review

Date: 2026-10-26. Source cycle 1.
Workspace: D:/dev/simple-coremux-shared-20261025.
Observed candidate HEAD: 1aaec595d0f49a0e255e27a6ebc5a7720f8cfa80.
STATUS: WARN / source-only; one adjacent legacy integration P2 requires correction.
No concrete scoped P0/P1/P2 was identified in the seven frozen L2 paths themselves.
Nine pure and two native cases are authored, zero executed. Fixture NOT_BUILT.
No compiler/build/test/native/helper/product execution, staging or commit occurred.

## Exact frozen inputs

Manifest build/review/smux-configured-launch-source-v1.sdn matched expected SHA256
33f1b46feb75bf45fbfa4163267623dc33134379b8b9ad8643f244cbb07983e0.
All seven listed hashes matched.

| Path | SHA256 |
| --- | --- |
| src/os/apps/smux/pane_configured_launch_service.spl | 74130fe5c96303f5aa84af8f9cfccb24675aba1776f084fc5960c96750a8c067 |
| test/01_unit/os/apps/smux/configured_launch_admission_spec.spl | ac97c67c3408573ddedc9030bf0a5c1efad2b28c5a0de20e35a72f6260d7fb85 |
| test/03_system/tools/smux_configured_launch_spec.spl | 40dc4923cec1ae64781e330a75c60798abc8aab120c43b53b987fc77416fa7cd |
| test/fixtures/coremux/configured_launch_child.spl | c22fd484cab1b235dfaa9454522eef50bf9742786eedd953d5d114e30d0f0f2d |
| doc/06_spec/01_unit/os/apps/smux/configured_launch_admission_spec.md | a292da4902d1a5e6fcf8278be6c639d5232baf23d397e682efb593bd27d8707c |
| doc/06_spec/03_system/tools/smux_configured_launch_spec.md | ca5972d1f9fd5e1d977445c9b952eaa7322d97b99ce5f8588883308d2182f9b3 |
| doc/09_report/smux_configured_launch_source_2026_10_26.md | 62bed7acd989d8842fc62c7a4c34fd27a617b0d3cbd729caa9d26404913c6ecc |

Additional root-owned reviewed input:
src/os/apps/smux/pane_io_service.spl SHA256
ac43ac651c0c0b5047f3d6d0233d7c53828f5bb41560ba7b7f5100ce180bf597.
Its delta imports the generic cleanup query and treats any nonzero aggregate
cleanup status after negative open as pending. Unrelated active client-context
work was excluded.

## P2: adjacent legacy negative-open marker bypasses publication

The corrected legacy pane_spawn_pty_state can now return cleanup_pending=true
with commit=false when open failed and provider-global quarantine remains.
At the inspected api.spl:601-605 caller, cleanup_pending pushes a PaneClosePending
marker, but _publish runs only when updated.commit is true. Thus this newly
reachable result changes closing authority without publishing its configuration
revision/closing-marker snapshot. The earlier retained-fd failed-spawn path
commits a changed pane record and did not expose this same branch.

Root was notified before source acceptance. A minimal correction must preserve
updated.state when commit=true and publish a real closing-marker change even
when the registry value is unchanged. Alternatively, aggregate-only quarantine
can remain exclusively in a properly retained provider-wide cleanup gate.
Do not invent a per-pane native token or per-request cleanup ownership from the
aggregate count. This review does not edit the active API lane.

## L2 source contract review

pane_configured_launch_admit checks all three identities, actual membership,
closing policy, retained PID/fd refusal, both attachment counters and dimensions
before native allocation. Individual dimension bounds precede bounded product
arithmetic. The pure helper is the same helper used by the effect path.

The configured spawn forwards the complete existing PtyLaunchV1 unchanged:
Exec/Shell choice, executable/argv, cwd and ordered environment Set/Remove values.
No parser, shell prefix, environment rewrite, executable search, pipe fallback,
foreign registry or public launch ABI is introduced. Common Mux request validation
belongs to the adapter before mapping; provider-specific validation remains below
this owner. The helper is not yet a public API/typed CoreMux launch route.

A failed open queries provider-global pending status and treats both positive
counts and unknown/sticky negative status as pending. It returns unchanged state,
commit=false and no fabricated pane token. That observation is global, not a
per-request attribution or authority grant.

Failed or nonpositive spawn results invoke checked close. Close=false returns
the exact fd attached with PID=-1 and commit=true, retaining native cleanup
authority and consuming the already reserved incarnation through with_pty.
Close=true returns the original state. Positive PID attaches the actual returned
PID/fd. Existing with_pty behavior preserves content for deferred-close ownership
and resets content only for a real child. Counter capacity is admitted before
either transition. Provider error details are deliberately not returned, avoiding
argv/environment/cwd disclosure.

Admission-refusal pending status is scoped to the exact requested pane ancestry;
it does not query or operate foreign native authority. The returned unchanged
snapshot remains an internal explicit-state value, not a public serialized handle.
The API integration must honor cleanup_pending even when commit=false and commit
each returned state once under its sole authority.

## Authored test and manual review

Nine pure cases use the actual admission helper. Synthetic PIDs/fds remain pure
record inputs and are never passed to native operations. Cases cover empty-owner
admission, closing/membership refusal, existing child and deferred handle refusal,
dimension/product bounds, exhausted counters and last available identities.

The Exec system case launches a separately built real fixture. The fixture
checks actual argv including empty/space/quote/backslash/Unicode/metacharacter
values, actual cwd, Set/Remove and inherited environment before emitting a success
marker absent from argv/environment. The marker cannot be supplied by command
echo. A bounded child lifetime supports actual presence and overwrite refusal.

The Shell case intentionally executes shell syntax through the configured Shell
provider; no command is fed to terminal input for echo. Its echo output proves a
running shell command, while ping keeps the owner live for cleanup observation.
This does not independently prove descendant termination.

Both scenarios retain returned state from capture and launch, attempt cleanup
before post-acquisition assertions, preserve a distinct second returned authority
if overwrite refusal regresses, check actual PID presence/absence and require
aggregate cleanup_pending exactly zero. Failure does not become a skip/pass.
The external owner Job/watchdog remains necessary: retry counts do not bound an
individual native call, PID reuse is possible, and aggregate zero alone is not
complete Job/resource proof. Failed-open quarantine without a pane token remains
an explicit external owner-stop responsibility.

The test-only app.io env/cwd facade is the approved existing fallback for missing
sync generic environment ownership. No copied provider, raw extern or cross-family
alias was added. Manuals state the fixture prerequisites, private Unicode-space
cwd, inherited sentinels, producer/runtime/fixture hashes and NOT_RUN evidence
honestly. No placeholders or mocked native success were found.

## Outstanding gates

The adjacent API publication P2 needs a focused source correction/review.
Actual native failed-close retention, failed-open quarantine, error suppression,
counter-ceiling behavior, descendant/Job cleanup and resource bounds remain
unexecuted. So do canonical docgen, runtime checks and configured provider binding.

The explicit-state helper does not by itself connect full API publication,
common typed launch validation, receipt semantics, startup support or all
39 CoreMux operations. No Running state is inferred solely from a positive PID,
and no runtime/provider qualification follows from this review.

## Focused adjacent P2 correction

Root changed only the relevant marker condition to
`if updated.cleanup_pending and updated.commit:`.
This prevents global-only pending status with commit=false from creating a
per-pane closing marker or silently changing the configuration authority.
The retained-fd failed-spawn path still has commit=true: it records the closing
intent and publishes the returned owned state through the existing sole commit.

The helper's failed-open nonzero cleanup observation and provider registry remain
intact. Their aggregate quarantine belongs to the provider-wide cleanup/stop
gate; the API does not grant pane-native authority or claim clean release merely
because no pane token was returned. The existing text Result still returns the
launch error. Eventual CoreMux composition must separately consume its richer
PanePidUpdate cleanup status.

P2 is closed in this precise source delta. No remaining scoped P0/P1/P2 finding
was identified. This is not a full API review: concurrent L1 imports and context
reconciliation changes are explicitly excluded and need their own review.

Exact reviewed API function: src/os/apps/smux/api.spl,
smux_pane_spawn_pty. SHA256 of its UTF8 function text with exactly one trailing LF:
7fb681d5b4bfb5ad9758c93a853ce04bf34907288072c3abf53fefae2056fd9a.
The condition change above is its only L2 correction. The seven manifest pins and
legacy pane_io_service pin remain as recorded. No repeat native/test execution or
staging occurred; WARN / NOT_RUN and all qualification gates remain.
