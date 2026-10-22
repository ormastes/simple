# Checking SMUX on Windows

Use native Windows for ConPTY evidence. A Unix PTY run cannot establish that
Windows shells, console handles, or ConPTY cleanup work. The hosted launcher is
`bin/smux.cmd`, delegating to `src/app/hosted_apps/smux_client.spl`.

Build Phase 2 first and then Phase 3 with the canonical bootstrap flow. For
each SMUX build retain the exact compiler path, SHA-256, matching provenance
and admission receipts, isolated output/cache directory, build command, exit
code, and linker diagnostics. An existing compiler file alone is insufficient.
Unadmitted diagnostic builds must be labeled as diagnostics. Never substitute
the Rust seed or call a Phase 2/3 compilation a general SSpec execution pass.

Once an admitted general pure-Simple runner is available, execute these specs
in compiled mode so scenario bodies actually run:

- `test/03_system/tools/smux_service_features_spec.spl`: real production service
  ownership, windows, split dimensions, validation, focus, and attachment slots.
- `test/03_system/tools/smux_windows_conpty_features_spec.spl`: real Windows shell
  output, two child processes, and same-process detach/reattach continuity.

Generate the mirrored manuals with `spipe-docgen`, require zero stubs, review
the scenario steps, then run `sspec-maintain scan` for both pairs. Authored
manual drafts are useful review artifacts but are not generator evidence.

The service API names `vertical`/`v` for division of columns and
`horizontal`/`h` for division of rows. These aliases are API conventions, not
compatibility with tmux's `split-window -h` and `-v` flags. Splits reserve one
separator cell and refuse an axis below three cells. Invalid resize requests
leave dimensions and resize metrics unchanged.

## Independent foreground owner

The compiled entry now has explicit `--serve` and `--request` modes. After
qualifying the executable and providers, one process runs
`smux.exe --serve 127.0.0.1:PORT TOKEN`; independent disposable clients invoke
`smux.exe --request 127.0.0.1:PORT TOKEN COMMAND ...`. Keep the token private.
The command arguments are passed as data; no shell wrapper is needed.

Commands include `new NAME`, `list`, `windows NAME`, `panes NAME`,
`select-window NAME WINDOW_ID`, `select-pane NAME PANE_ID`,
`new-window NAME TITLE`, `split NAME DIRECTION`, `send NAME COMMAND ...`,
`capture NAME`, `attach NAME CLIENT_ID`, and `detach NAME CLIENT_ID`.
Pane commands address the selected window and focused pane. Wrong-session
detach refuses to remove another attachment. Request failures return a
nonzero process exit code.

Select geometry with `layout NAME LAYOUT COLS ROWS`. Layouts are
`even-horizontal`, `even-vertical`, `main-horizontal`, `main-vertical`, and
`tiled`. `rects NAME` reports pane-id/x/y/cols/rows, and `screen NAME` returns
a plain composite from actual VT cell snapshots. The RPC canvas is bounded to
512 columns, 256 rows and 60000 cells. UTF-8 replies have a separate 65536-byte
limit and can fail even when cell geometry fits. Split/close/arbitrary resize
invalidates the old named plan; select a layout again before composite capture.

The owner drains panes even without request connections. `stop-server` is
authenticated and closes its resources; request EOF closes only that request
socket. These source contracts await Windows execution. They do not establish
automatic daemon launch or survival of the owner's own console/job exit.

Additional acceptance specs are `smux_named_layouts_spec.spl`,
`smux_service_layouts_spec.spl`, `smux_protocol_features_spec.spl`, and
`smux_windows_owner_lifecycle_spec.spl`, all under `test/03_system/tools/`.
The live-owner fixture needs `SMUX_TEST_BINARY` pointing to the exact admitted
compiled executable. Its release-file-controlled flood checks detached work
without requesting captures during the interval.

Do not infer independent terminal clients, a detached daemon, unbounded
background output, live child resize, copy mode, or scrollback history from
these scenarios. Those require separate implementation and external runtime
evidence. The hosted stdin loop currently destroys its service on EOF;
in-process attachment continuity does not establish client-exit survival.
