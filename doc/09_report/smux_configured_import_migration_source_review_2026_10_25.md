# Smux configured import migration source review

Independent bounded review against frozen baseline
`0c74b566af53b95a548f24bd9c34c7fa34771df6` in
`D:/dev/simple-smux-system-execution-20261025`.
**Status: WARN / source review complete.** No concrete P0/P1/P2 finding in the
17-file migration. Compiler launches and native executed test cases: **0**.
Source equivalence is not application-body execution or runtime qualification.

## Equivalence and owner selection

An independent case-sensitive source comparison reconstructed each candidate
from its baseline using only an anchored import-prefix replacement:
`use std.nogc_sync_mut.` becomes `use std.`. All14 application files matched;
the diff contains exactly26 prefix substitutions. Line-ending normalization
was used for that textual comparison, not as permission for other changes.
Imported symbol lists, aliases, declaration signatures and all bodies remain
identical. No family-qualified references remain elsewhere in these14 files.
All candidate fingerprints match the migration manifest.

The committed semantic selector maps explicit `nogc-sync-mut` to `gc_off=true`
and allowed families `nogc_sync_mut, common`. The committed resolver uses the
retained application owner and explicit policy, preserves configured provider
facades, and searches the selected family plus common rather than another
runtime family. Invalid importer context and missing selected owners diagnose.

The ten expected owners for generic `std.sosix.*`, `std.io.crypto_sffi`,
`std.io.tcp` and `std.tmux.mod` exist at the retained NoGC Sync Mut paths and
match every owner hash in the manifest. No matching direct generic facade was
present at the documented library/provider roots for these modules. This
supports the same owner selection under the explicit mode at source level;
compiled resolution, overlays and ABI receipts remain NOT_RUN.

Physical imports inside library implementations and direct ABI/provider test
boundaries were not part of the migration and were not rewritten. Concurrent
runner transport files were excluded from this review; their acceptance is
neither inferred nor claimed here.

## Recipes and evidence boundary

Both recipes require semantic `--library-mode nogc-sync-mut` for the product and
actual generated SSpec runner, using generic source roots and a separate Windows
provider overlay. They do not pin a physical family root or substitute a custom
test engine. An unsupported older compiler or missing runner forwarding is
explicitly BLOCKED, with no compiler/profile/family fallback. Missing other
profile owners remain diagnostics, not a request to copy facades.

The migration deliberately does not establish the moving test-runner transport.
Future acceptance requires actual compile argv/typed selection, admitted
producer and runtime identities, real case/assertion counts and terminal
cleanup receipts. No authored or structural check is counted as a native PASS.

## Exact frozen SHA256

| File | SHA256 |
|---|---|
| src/os/apps/smux/api.spl | b47fc352231f1f5544b3270dfb3a30b4c19058942937633ce91cdf91f0a3a384 |
| src/os/apps/smux/child_lifecycle.spl | 3c19f7b87762bacaffa428bdefcf400a7d4dc4d1e87ae020f4e92861e1ad4bbf |
| src/os/apps/smux/pane_io_service.spl | 93697cc2c5c7887b055ac09e180c69075588a6c8502957d7002ac619888410ad |
| src/os/apps/smux/window_layout_service.spl | 26c85f716c5aac8f49c7984edb0f7727426fc8bca4992c27356af65de6e585d4 |
| src/os/apps/smux/interactive_client.spl | 716f0df21471f314d309d32bb3fdf125f9257f966440f1db225eaf226c9daa6c |
| src/os/apps/smux/interactive_protocol.spl | b541139cf9d0d760862c26b67e29d41d24147ccd55b0e38485fc85905c74b3f8 |
| src/os/apps/smux/smux_app.spl | 7d821c53584f2adee693b9bdaa28c01c2b3764d156d1aae7f886e3921a0c1606 |
| src/os/apps/smux/smux_remote.spl | 7715659de676be4e4397f2408a99d81c67c256100b7da3c87a238705067c2bd6 |
| src/os/apps/smux/server.spl | 91f822de39b477c314ecdb0627a583c294761f3a847b2905950de69fc1ec79d1 |
| src/app/hosted_apps/smux_client.spl | fb0aeed2d073d13fa753e5123d0223b7215680a53c211f826e6d5891b8e87648 |
| src/app/web_dashboard/server.spl | 48eb2fe556ab1d4c79fe957d47dfabab0c473f5dba07ad0d98924db5ff41b496 |
| src/app/web_dashboard/tmux_api.spl | ff6259bb57cea3d9981c1a0fe489f4fcd4e227e02013b0fa3fceeb440792c294 |
| src/app/llm_dashboard/web_login.spl | 539e290cea87858248b4402804dbf3ac5b3e506260a2c4eccb3d1df7cd4b9697 |
| src/app/llm_dashboard/login_only_server.spl | 4f3ebd6a2efc68fb1e6d4b2939e9970e38ff9d40be2a952f4fc85fa365ddd400 |
| doc/03_plan/sys_test/smux_major_features_phase3.md | 22a7474ccd38e7d4c91e5e653ac93df36451997ead99d398debb8388acdc1347 |
| doc/03_plan/sys_test/smux_window_lifecycle.md | cc00337805f91c57ac09a25fa03ba402ee37a6d5b188903449922c7559844be4 |
| doc/09_report/smux_configured_import_migration_2026_10_25.sdn | ef3b80b27f00bd992e83510cfbf642820b805b8db9bbd8944b80b81bd9eed0ad |
