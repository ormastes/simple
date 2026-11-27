# DAE-05 source foundation provenance

Status: exact source overlay; native exports and runtime are NOT_ADMITTED/NOT_RUN.

Root authorized six SPL dependencies from frozen INDEX27 SHA-256
`1902626e76e591c087a1aa28cdc8d1e5bf7884add5c0d477e7f493804a0f9584`.
Immutable mirror: `/tmp/dae05-foundation-1902626e-b3gj74a7`.
Source index: `/home/yoon/dev/simple-parallel-podman-ci-20261107`; it was not modified.
No C, app, Host domain, test, or policy foundation file was copied.
Final integration depends on the separately reviewed foundation, not this overlay.

These baseline bytes are not checkpoint implementation changes. Review subsequent
checkpoint deltas against the baseline hashes below, not against release HEAD.

| File | Foundation SHA-256 | Pre-overlay HEAD SHA-256 |
| --- | --- | --- |
| src/lib/common/task_runner/distributed_operation_journal_v2.spl | `296431d2a4aeb034543fe2e4cc5a02f9ae12dd2ec0f91ff6295a19c807716c50` | `e66b186d012d5ddfe66f74fe262a0506c6bd7823e61aef0bf051dbe6bad6e1e2` |
| src/lib/nogc_sync_mut/database/wal_segmented.spl | `02e89b17572ce462fca712b13d4d73604ac5bf02cf03284270b46d3fc97dfd44` | `36181c9cd27d4557e1ccf9e4bf2753e18318fad89f0d067dcba33095a7b448ec` |
| src/lib/nogc_sync_mut/database/wal_storage_v2.spl | `d0f0b3915146ce8b792248ad51514dbaa9e73ff200ac446e4ab286f4e90b6cf5` | `absent` |
| src/lib/nogc_sync_mut/io/windows_journal_store_v1.spl | `a173f7c64b14f5d76389f794ce04a90c9b6f8a5332da52ee2c2f9f63a3cff405` | `absent` |
| src/lib/nogc_sync_mut/io/windows_private_file_abi.spl | `9ddf455f67de510fa38eedf6e37e915cdda492ba75ee4f84790c76fed70c6d09` | `948d83d4bece82e589643794bd97d081108179ccadc36ddfda7fdd6f9246d688` |
| src/lib/nogc_sync_mut/io/windows_private_file_v1.spl | `baccbf13458fa0e8a271e59028f0471ef48e42e9dd825561ca01bcc3d064ea80` | `3ab3b19830398d7af20162b5ca9d0376ada3a803e67c7baa754a370977af43c2` |
