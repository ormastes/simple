# Target 5 direct compiler I/O ownership (2026-09-28)

The compiler still imported the broad `app.io` compatibility hub for file,
process, and environment operations. The hub re-exports existing
`std.nogc_sync_mut.io` owners and also imports app-only CLI facilities. Nine
module-level imports now name their file/process/environment owners directly.
Four function-scoped imports were moved to module scope with the same symbol
aliases because function-scoped `use` is not a reliable native symbol-binding
site. This removes the broad app hub from those compiler source closures.

The widened kernel closure check covered 2,086 compiler files and reported
23 kernel-to-app/OS edges before this change and 10 afterward. The earlier
facade cleanup began at 35. The other categories stayed at 3 K0-to-P,
14 K1-to-P, and 2 unresolved edges. The command still exits nonzero; its
retained output is `build/mini_builds/target5_kernel_closure_direct_owners_2026-09-28.log`.

No startup, RSS, or binary-size claim follows from an import count alone.
Target 5 still needs direct plugin-edge removal, demand-loaded provider
activation, a qualifying self-hosted runtime, and matched size/startup
cohorts. The remaining compiler-to-app/OS edges include worker transport,
interpreter JIT/LLVM helpers, and loader/SMF integration, which need explicit
ownership boundaries rather than another broad import rewrite.
