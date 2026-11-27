# Windows owned execution scope

Owners: resource_scope, windows_redirected_process and windows_process_owner in
std.nogc_sync_mut.io. Preserve bounded child-tree admission, lease retirement
and capture cleanup. Apps use the existing facades.

See [bounded admission evidence](../../../08_tracking/bug/windows_owned_scope_admission_2026_10_25.md).
TMPDIR/TEMP and recursive drive-root creation were repaired. Native environment
assignment validation still fails; checked admission preserves its reason.
The six-attempt resource repair budget is exhausted. No child-launch, SSpec,
platform promotion or release PASS is established.
