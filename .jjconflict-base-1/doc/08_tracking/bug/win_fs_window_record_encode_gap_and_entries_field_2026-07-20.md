# `lib.common.win_fs.window_record`: missing `window_record_encode` + internal `WindowRecord.entries` field mismatch

**Date:** 2026-07-20
**Component:** `src/lib/common/win_fs/window_record.spl`,
`src/lib/common/win_fs/fs_encoder.spl`,
`src/app/simple_process_manager/winfs_shim_host.spl`
**Severity:** Medium — blocks the window-registration RPC contract test and
one publish-path test in `simple_process_manager`
**Found by:** whole-suite triage campaign, `test/02_integration/app/simple_process_manager/`

## Finding 1: `window_record_encode` imported but not defined

`test/02_integration/app/simple_process_manager/spm_service_spec.spl` line
20 imports:

```simple
use lib.common.win_fs.window_record.{WindowRecord, WindowState, Rect, BufferRef, window_record_encode}
```

and calls `window_record_encode(rec)` (lines 79, 81) to build/verify an RPC
body for the "AC-3: window_register RPC uses the shared record body
contract" example. Actual: `error: semantic: function
`window_record_encode` not found`. Confirmed by reading
`src/lib/common/win_fs/window_record.spl` directly — `WindowRecord` (fields:
`wid`, `generation`, `app`, `title`, `state`, `geometry`, `buffer_ref`,
`acl_id_path`) and its `static fn new(...)` constructor exist, but no
`window_record_encode` free function is defined anywhere in that file (nor
elsewhere under `src/lib/common/win_fs/`). This is a genuine missing
symbol, not an evaluator-resolution quirk — the function does not exist in
source.

## Finding 2: `WindowRecord` has no `entries` field, but encoder code reads `tree.entries`

`test/02_integration/app/simple_process_manager/winfs_shim_host_spec.spl`'s
"AC-4: publish writes /<app>/<wid>/title under runtime dir" example fails
with `error: semantic: class `WindowRecord` has no field named entries`.
`WindowRecord` genuinely has no `entries` field (see field list above). The
`.entries` accesses that would trigger this live in
`src/lib/common/win_fs/fs_encoder.spl` (lines 35, 80, 81, 89, 90) and
`src/app/simple_process_manager/winfs_shim_host.spl` (lines 58, 60), all
operating on a value named `tree` — consistent with an `FsTree`/entry-list
type, not `WindowRecord`, being the intended receiver. The failure suggests
a `WindowRecord` value is being passed where an `FsTree`-shaped value
(something with an `entries: [FsEntry]` field) is expected, somewhere in
the `winfs_shim_host.spl` publish path.

## Affected specs

- `test/02_integration/app/simple_process_manager/spm_service_spec.spl` —
  1 example (Finding 1); this file also has 2 unrelated failures from the
  already-documented `unknown static method` landmine
  (`AuthorityToken.public_none`, see
  `generic_class_static_method_unresolved_under_test_2026-07-20.md` —
  referenced here, not re-filed)
- `test/02_integration/app/simple_process_manager/winfs_shim_host_spec.spl`
  — 1 of 3 examples (Finding 2)

## Root-cause hypothesis

Both findings point at the same area (`win_fs` window/publish encoding)
having drifted: either `window_record_encode` was planned but never
implemented, or was renamed/moved and the `use` import wasn't updated: and
the publish path in `winfs_shim_host.spl` appears to conflate a
`WindowRecord` with an `FsTree`-like `entries`-bearing type at some call
site. Not root-caused to the exact call site or fixed here (source-reading
triage only, no Rust seed changes attempted).

## Note

Both spec files left unmodified — the imports and field accesses reflect
what the contract is supposed to be; fixing this means implementing/wiring
`window_record_encode` and correcting the `winfs_shim_host.spl` publish
path, not editing the tests.
