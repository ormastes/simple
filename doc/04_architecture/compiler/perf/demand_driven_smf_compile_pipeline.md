# Architecture — Demand-Driven SMF Compile Pipeline

## Decision

Use one layered pipeline:

`SCV snapshot -> package index -> persisted action graph -> SMF metadata proxies -> demand HIR -> closed MIR -> bytecode/Cranelift -> asynchronous LLVM promotion`.

## Layers

1. **Snapshot owner** freezes canonical paths, content digests, and revision. No later layer reads the live worktree.
2. **Package-index owner** maps files to packages and stores import/reverse-import/SCC edges and semantic digests.
3. **Action-graph owner** schedules immutable actions, pools CPU/memory/device resources, and commits child results deterministically.
4. **SMF archive owner** publishes sectioned package/class images. Readers open the header/index first and map only requested sections.
5. **Import materializer** exposes `Unrequested`, `MetadataReady`, `BodyReady`, `MirReady`, `NativeReady`, and `Failed` states with single-flight transitions.
6. **HIR request owner** records required operations and bodies. It permits abstract/deferred bodies but not invented types or semantics.
7. **MIR admission owner** accepts only a fully materialized, type-closed dependency set and rejects proxies.
8. **Backend owner** returns baseline bytecode/Cranelift synchronously and publishes LLVM/native promotion asynchronously.
9. **Artifact service library** provides queue, leases, cancellation, compatibility IDs, stdio framing, and receipts. Compiler and test-runner daemons are thin profiles over this library.
10. **Common async file-view owner** is the primary Simple file-reading boundary. It attempts read-only mapped windows by default and otherwise serves the same bounded ranges through asynchronous buffered reads. Callers select policy but never branch on transport implementation.

## SMF package image

The header contains schema, package/action/compiler/target/config identities, dependency interface digests, section directory, and checksums. Sections are independently hashed and mapped:

- exports and symbol index;
- import edges and required capabilities;
- type/layout shapes and dictionaries;
- generic/inlining bodies;
- deferred HIR body chunks and operation summaries;
- MIR/function/object chunks;
- initialization/provider/aspect/reverse-reference summaries;
- diagnostics/debug/source maps;
- provenance and qualification receipts.

## Lazy import contract

Head scanning may identify package/import declarations and reject unsupported constructs, but it is never semantic authority. An SMF proxy answers only facts present in verified metadata. Requests that need absent facts enqueue materialization and suspend through the existing promise/task runtime while source code remains synchronous-looking. Cycles become deterministic SCC tasks. Failure is cached for the action identity.

## Robustness boundaries

- No speculative placeholder crosses into MIR.
- No daemon-owned heap object is persisted as authority.
- No hidden recursive scan fallback exists.
- Drift creates a new snapshot/action; it never mutates an active build.
- Background optimization may publish a better artifact only under the same semantic action identity and compatible backend identity.
- GPU parsing cannot become default without fixture-specific crossover and transfer-inclusive evidence.
- `mmap` is the preferred transport, not a correctness dependency unless the caller selects `must_map`. Under `auto_map` or `prefer_map`, mapping failure falls back before publication to the portable asynchronous range reader; active readers never mix two file identities or observe live-file drift.

## Common file-I/O policy

`FileReadPolicyV1` has four explicit values:

- `auto_map`: default; map when capability, file kind/size, access locality, and address-space budget indicate benefit.
- `must_map`: require a stable read-only mapping and return a typed unsupported/admission/resource error otherwise.
- `prefer_map`: attempt mapping first, then use asynchronous buffered reads.
- `buffered`: prohibit mapping and use asynchronous buffered reads directly.

The owner may map a whole small file or bounded windows of a large file. SMF, compiler, parser, test runner, database, and ordinary library callers use this common boundary rather than private `mmap` wrappers.
