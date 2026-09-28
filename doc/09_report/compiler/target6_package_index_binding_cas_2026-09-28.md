# Target 6 package-index binding publication race (2026-09-28)

`compiler_entrypoint_admit_v1` reads the current package-index pointer before
publishing its binding-only fallback. Without a compare-and-publish operation,
a graph writer could publish between that read and the fallback's pointer
rename; the fallback would then erase the graph and make the next request cold.

`package_module_index_publish_if_current_v1` now compares the expected pointer
under the same file lock used by ordinary index publication. An empty expected
digest means the pointer must be absent; malformed or unreadable existing
pointers reject the comparison. Immutable content is written before the
pointer rename. Admission uses this operation for its binding-only fallback.
If another writer wins, admission rereads the pointer and accepts it only if
it binds the same SCV snapshot; otherwise it fails closed. The warm read path
does not acquire this lock.

The no-stub native probe
`test/fixtures/compiler/package_index_publish_cas_native_probe.spl` built
28 units with the admitted pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
The probe binary SHA-256 is
`dac6864b560ff4416bd7b28ed4a97b14f4844d2d7f862e2171b4658f58958676`.
It exited 0 after binding publication, graph upgrade, rejection of a stale
binding write, and readback of the intact graph pointer. The matching SPipe
unit file reported `3 passed, 0 failed` through the bootstrap interpreter;
its stale `app.spipe.testing` import was replaced with `std.spec` to make the
examples executable. Logs and binary are retained under
`build/mini_builds/target56_package_index_cas_*`.

A second no-stub native probe links the production
`compiler_entrypoint_admit_v1` closure (111 source units, SHA-256
`4c3495f68483fc8d47ff4fe2739087b1b43f02c6a8c0d7fe2f503808cb710b40`).
It passed cold and warm admission in a committed one-source Git fixture with
an isolated `SIMPLE_CACHE`, then read back the matching binding-only index.
This proves the new compare-and-publish call is linked and usable from the
entrypoint on this focused fixture. The retained binary and log are under
`build/mini_builds/target56_package_index_admission_*`.

This closes the specific fallback-overwrites-graph race. It does not produce
the typed TLDR/SMF/archive facts, publish a graph from the production driver,
qualify concurrent graph writers, or satisfy the Target 6 performance gates.
