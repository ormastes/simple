# Pure-Simple CLI completeness architecture

CLI dispatch remains pure Simple. Executable identity uses scalar argv runtime
primitives; file staging uses `app.io.file_ops.file_write`; filesystem walking
adapts `rt_dir_walk` paths locally into `DirEntry`. Rust remains runtime support,
not an alternate CLI implementation.
