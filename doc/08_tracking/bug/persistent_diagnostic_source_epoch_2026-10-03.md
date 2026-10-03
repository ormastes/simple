# Persistent diagnostic source epoch

Source implementation only; native/spec/performance qualification is UNRUN.

The index image cannot compile a sequence of individual entries by repeatedly
calling the full-inventory loader: that decodes and selects the complete
inventory for every task. Pre-populating `ctx.sources` is not a solution because
`compiler_driver_run_compile` invokes source loading again.

The adapter first performs canonical admission and calls
`driver_admitted_epoch_begin_v1(NativeFullInventorySourcesV1)`. This is an
internal trusted-call boundary, not authentication of an external struct. The
epoch binds eight published SCV fields and builds immutable identity/hash/length
maps once. Task requests carry only an identity; they cannot replace a source
digest or root. One process owns one serial epoch. Parallel workers own separate
epochs. Owner handles increase across epochs and overlapping tasks are refused.

`driver_admitted_epoch_compile_v1(owner, identity, options)` accepts AOT/SMF
diagnostics, creates a fresh compiler context and enters the existing explicit
entry/import-closure loader. Only an active internal task bypasses repeated
package-index and snapshot admission. Resolver roots and physical module names
use the retained snapshot root; manager cwd remains the output work directory.
All source reads in that loader, including cached scans and raw bulk/default
read seams, pass through the retained map and a bounded no-follow read. The
buffer hashed is the buffer scanned and installed in the source context. An
admitted dependency remains a required probe after deletion, so it cannot
silently resolve to a parent facade instead.

Authority/read errors are sticky and return `Err`; restoring environment cannot
recover that epoch. Ordinary compiler failure returns `Ok(CompileResult failure)`
after settling the task and releasing its scan cache. The next task has a fresh
context. Ending an active task is refused. Process termination cancels ownership;
there is no transferable validity boolean, thread sharing, or external epoch
token. Canonical outer producer/runtime/task-schema admission remains required.

The source-only read audit found that parser phase two consumes retained source
content arrays/SourceFile buffers; it does not reopen source paths. No parser
child is launched by this wrapper. Five inherited parse/HIR sharding selectors
are rejected before compilation. LLVM/Cranelift are the only supported backend
labels; bootstrap native overrides are rejected. This matters because those
native dispatch branches precede the AOT pipeline's SMF-format branch. With
these restrictions, native capsule freezing (which can reopen reclaimed source)
is not on this diagnostic path. Native qualification must still execute the
concrete mode/environment rather than infer correctness from this source audit.

## Qualification boundaries

The focused spec covers retained map counters across task cache release,
private-to-admitted cache transition, same-length tamper, actual transitive
unlisted dependency rejection through `load_sources_impl`, retained dependency
bytes after disk mutation, path escape, duplicate rows, cleared binding,
overlap/stale handles, path normalization, and ordinary compile failure followed
by a clean task. These are executable tests, not executed PASS evidence.

Fresh contexts and removal of references do **not** establish bounded native
allocation across thousands of tasks. Existing per-file parser transient scopes
remain unchanged. No unsafe whole-compile transient scope was added. A native
multi-task resident-growth measurement and escaped-root review remain necessary
before claiming persistent-worker memory readiness. File no-follow applies to
the leaf; canonical-path confinement is checked before the verified read, and
the same-byte digest protects consumed content. This is not a new filesystem
watcher or a full-checkout cleanliness proof.

No frozen producer/source or live queue was changed. Old e589 and unmodified
a090 images do not contain this source hook merely because source files exist.
