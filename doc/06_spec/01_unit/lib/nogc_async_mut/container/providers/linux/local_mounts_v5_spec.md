# Linux local mount V5 regression manual

Status: **AUTHORED_NOT_RUN**. No compiler, runtime, bootstrap, or engine campaign
was performed. The parent session's six-cycle qualification cap remains in
force; the canonical runtime is unavailable. Source review is not runtime PASS.

Executable source:
`test/01_unit/lib/nogc_async_mut/container/providers/linux/local_mounts_v5_spec.spl`.

Reproduction: a local request needs `/host/work tree` bound read-write to
`/work`. The historical Linux request cannot retain this mapping. Reusing build
roots silently changes the guest destinations to `/simple-build/inputs` and
`/simple-build/outputs`. V5 instead retains the exact mapping and permissions,
binds them into immutable request identity, and refuses effects until an actual
native mount-admission owner exists.

Authored assertions cover exact canonical roundtrip and spaced/empty argv;
digest changes for source, guest, permissions and order; downgrade, tampering
and unknown-field rejection; traversal, injection, root mounts, overlapping
targets, count bounds and legacy-root conflicts; replay and create refusal
with zero executor calls; empty command output from direct builder refusal;
and default empty mount omission with the legacy create path still available.
The separate exec adapter also rejects a mounted parent before opening its
engine owner or journal. The downgrade fixture includes a valid containment
digest so it isolates the mount-version gate rather than an earlier V4 check.
Existing `oci_user_selection_v3_spec.spl` provides frozen V1/V2 byte/digest
compatibility assertions; existing codec/containment specs cover V3/V4. None
was rerun for this source-only slice.

Expected effect result for nonempty mounts:
`linux-mount-native-admission-not-installed`. This is an explicit unsupported
result, not successful workspace launch or completed migration. The current
action projection is also fenced by provider validation. A future qualification
campaign must prove authorized source identity survives engine reopen and
reject symlink/rename substitution before changing this limitation.
