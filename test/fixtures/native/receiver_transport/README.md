# Cross-module native receiver transport

This bootstrap-only probe isolates receiver transport from the capsule fixture.
`local.spl` checks a typed local receiver. `typed.spl` checks a receiver passed
through a typed free-function parameter, then a method with ten total arguments
(self plus nine integers, including two AArch64 stack arguments).

The tracked support signatures spell out `self`. Both entries exit zero and
print their calculated values (107 and, for typed, 145). A nonzero result is a
failure; compiler exit zero alone is insufficient.

The red inputs are exactly these same three source files with the two `self, `
parameter prefixes removed from `support.spl`. That valid implicit-self spelling
triggers the bootstrap producer's parser/import-arity disagreement. Both red
entries build but exit 139. Red disassembly drops self, including from a typed
parameter. Green disassembly retains x0 and emits both required stack stores.

Build each entry using `<authority>/simple`, the frozen bootstrap-only producer whose SHA-256 is
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Use its matching `stage2-runtime-authority`, the retained LLVM 23 environment,
and `native-build --backend cranelift --runtime-bundle core-c-bootstrap
--runtime-path <authority> --entry-closure --threads 2 --cache-dir <private>
--mode one-binary --entry <entry> --output <output>`.
Set `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB=<worktree>/src`.
Wrap builds and runs with `scripts/resource/process-tree-rss-watchdog.pl`,
`--max-rss-kib=5859375 --interval-ms=100`, timeouts 180 and 20 seconds,
separate receipt paths, and `/usr/bin/time -l`.

Recorded evidence and scope limits are in
`doc/08_tracking/bug/bootstrap_implicit_receiver_import_arity_2026-09-22.md`.
This fixture proves the explicit-receiver containment only. It does not repair
implicit-self support in the compiler or admit any bootstrap phase.
