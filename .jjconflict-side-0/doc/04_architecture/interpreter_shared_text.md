<!-- codex-architecture -->
# Interpreter Shared Text

## Status

Proposed. This design is a prerequisite for implementation; it does not change
the language or runtime ABI by itself.

## Context

The Rust seed interpreter represents text as `Value::Str(String)`. `Value`
object fields use `Arc<HashMap<...>>`, but field-map COW deep-clones every
contained `String`. The real executor characterization in
`interpreter_call/block_execution.rs` proves that changing only a CoreLexer-like
`pos` field clones an 8-byte and a 1 MiB `source` buffer. The parser consequently
misses its 22 KiB `<15s` gate (latest: 27.631s).

Static inventory finds 925 `Value::Str` uses across 102 files: approximately
531 constructors, 408 borrowed patterns, and 56 owned-string boundaries.

## Decision

Use one coherent internal representation:

```rust
pub type SharedText = Arc<String>;
Value::Str(SharedText)
Value::text(value: impl Into<String>)
Value::shared_text(value: SharedText)
```

`SharedText` is immutable shared storage, not interning. `Value::clone` clones
the `Arc`; equality, ordering, hashing, keys, display, indexing, and slicing
remain byte/content based. Text-producing operations allocate a new
`Value::text`; production code must not use `Arc::make_mut` or `Arc::get_mut`
on `Value::Str`. Existing shared values use `Value::shared_text` or direct Arc
clone so they are never round-tripped through `String`.

Symbols remain `String`. FFI borrows text pointers only for call duration and
wraps returned owned bytes as new shared text. Runtime, JSON, SDN, bridge, and
cache representations serialize bytes only; Arc identity never crosses a
boundary. There is no C ABI or on-disk schema change.

This is a central value-representation change, not an MDSOC capsule: one mixed
or parallel string variant would multiply exhaustive matches and risk divergent
semantics.

## Migration Boundary

1. Land the `SharedText` alias, `Value::text`, and fail-fast semantic tests.
2. Change the variant and clone owner and add `Value::shared_text` in one
   coherent compile-fix change; adding that helper earlier would deep-copy.
3. Fix semantic owners: key/display/equality, concat, Unicode index/slice, then
   runtime/value bridges.
4. Mechanically convert constructor sites; borrowed patterns normally remain.
5. Verify focused semantics, workspace compile, RSS, and parser performance.

Rollback is the whole shared-text representation change. The accepted lexer
source cache and interpreter global-index fixes remain independent.

## Acceptance

- Cloned text keeps the same Arc/source-buffer identity.
- Explicit aliases remain unchanged after concat/case/replace/slice operations.
- Content equality, key/display, Unicode index/slice, FFI, and serialization
  remain exact.
- Executor field-map COW still occurs, but its source buffer remains shared.
- Representative short-text and parser workloads regress max RSS by no more
  than 10%.
- A source/test guard rejects `Arc::make_mut` or `Arc::get_mut` on
  `Value::Str` storage.
- The 22 KiB parser fixture exits 0 and completes under 15 seconds before any
  493-source bootstrap shard.

## Consequences

Large immutable fields become O(1) to clone. Each unique short string gains an
Arc control block/refcount cost, hence the mandatory RSS gate. Roughly 531
constructor sites require mechanical conversion, but only value semantics,
concat, and bridge boundaries require design judgment.

## Collaboration

- Spark discovery: constructor/boundary inventory and migration ordering.
- Spark test: fail-fast semantic and identity gate plan.
- Merge owner: `/root`.
- Final reviewer: `higher_source_review`.

## References

- `src/compiler_rust/compiler/src/value.rs`
- `src/compiler_rust/compiler/src/value_pointers.rs`
- `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
- `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`
- `doc/08_tracking/bug/bootstrap_parser_quadratic_source_refetch_2026-07-12.md`

## Reproducible RSS Evidence

Record pre/post evidence in
`doc/09_report/perf/interpreter_shared_text_rss_<phase>_2026-07-13.md` using the
same release-seed binary/build mode and `/usr/bin/time -v`:

```text
timeout 90s /usr/bin/time -v env SIMPLE_LIB=$PWD/src \
  src/compiler_rust/target/release/simple run \
  test/fixtures/parser_token_text_scaling/main.spl

timeout 90s /usr/bin/time -v env SIMPLE_LIB=$PWD/src \
  src/compiler_rust/target/release/simple run \
  test/fixtures/interpreter_shared_text_rss/main.spl
```

The second fixture retains many distinct short strings, not clones of one Arc.
Each post-migration maximum RSS must be <=110% of its own baseline. The parser
command supplies RSS evidence only; the already documented 27.631s remains the
pre-migration timing baseline.
