# Clang native barrier needs strict parent admission

Status: open. Scope: `src/app/build/clang_policy/native_rebuild_barrier.spl`.

The barrier checks mapped directory ancestors with `path_absolute`. On POSIX,
the runtime calls `realpath`, but if resolution fails it returns the original
absolute input. Equality with a protected path therefore cannot prove that
the ancestor was resolved. A mutable symlink or inaccessible ancestor could
make deletion follow a path that was never strictly admitted. The current
build-root lock protects only cooperating builders, not hostile writers.

Before connecting the barrier to production CMake/Ninja execution, add a
strict no-follow directory primitive with an explicit failure result. It must
walk from an admitted root using directory handles, reject links and reparse
points on supported hosts, and keep the handle-based ownership through object
invalidation. The pure-Simple controller should call that narrow host boundary
and reject the action on any failed check. Validate POSIX symlinked-ancestor,
rename-race, permission-failure, and Windows reparse-point fixtures. Then run
the focused Simple spec and the native build qualification in a fresh session.

Related: `doc/03_plan/compiler/build_system/dist_build_scheduler_2026-09-25.md`.
