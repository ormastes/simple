# Target 5 compiler I/O facade closure cleanup (2026-09-28)

The widened kernel closure checker found compiler backend and linker modules
importing `app.io.sysinfo_ops` and `app.io.file_ops` compatibility facades.
Those modules only re-export the existing `std.nogc_sync_mut.io` owners.
Eight `getpid` imports and three file-operation imports now name the stdlib
owners directly. `link.spl` also imports `shell` from the stdlib process owner
at module scope; its old function-scoped `use app.io.process_ops.shell` could
not reliably register the symbol under native compilation.

The fail-closed closure check covered 2,086 classified compiler files. Before
these edits it reported 3 K0-to-P, 14 K1-to-P, 35 kernel-to-app/OS, and
2 unresolved edges. Afterward it reported 3, 14, 23, and 2 respectively.
The retained logs are under `build/mini_builds/target5_kernel_closure_*.log`.
The overall checker still fails; this is a twelve-edge reduction, not a
kernel-partition qualification pass.

These import changes do not establish a binary-size or startup improvement.
The full self-hosted CLI and a matched size/startup cohort are still required
to prove Target 5's demand-loading and size gates. The remaining closure
violations include direct VHDL plugin imports and compiler-to-app/OS imports;
they require separate ownership and dispatch work.
