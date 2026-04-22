# SPM Privilege Check Task Mirror Design

Feature: FR-SPM-0002.

## Design

`spm_priv_check_for_task(task_id, id_path)` is the pure helper for testing and
handler reuse. It rejects empty id paths, looks up the caller's cached mirror,
and runs the existing two-gate prefix/authority check.

The syscall dispatcher passes `caller.id` into `_handle_spm_priv_check`, so the
handler no longer depends on a global current-task side channel.
