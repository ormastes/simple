# WM tray typed window rows spec

Executable source: `test/02_integration/app/wm_tray_typed_window_rows_spec.spl`.

The spec compiles the production tray module through a no-stub native entry
closure and runs its daemon-free `status` command. The whole module must pass
HIR lowering, including its list and quit-all branches that iterate typed
`WindowInfo` rows. The status command must return zero.

The 2026-09-28 native execution reported one example and zero failures. See
`doc/09_report/compiler/target56_stage4_cli_link_boundary_2026-09-28.md`.
