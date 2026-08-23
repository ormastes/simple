# Seed: every call frame heap-allocated its own EMPTY `global_bindings` map

- **Date:** 2026-08-23
- **Component:** Rust seed, `CowEnv` (`src/compiler_rust/compiler/src/value.rs`)
- **Class:** duplication of data already owned / per-call allocation
- **Status:** FIXED

## Symptom

`CowEnv::new()`, `CowEnv::from_map()`, `CowEnv::with_base()` and `CowEnv::clear()`
each did:

```rust
global_bindings: Arc::new(HashMap::new()),
```

`CowEnv::new()` / `with_base()` run on **every function call**, so every frame
paid a heap allocation (an `Arc` control block plus a `HashMap` header) for a
map that is empty in the overwhelming majority of frames: `global_bindings` is
populated only by selective lambda capture and by tests — the module scope
answers the same question lazily for every other name.

## Why it survived the sibling fix

`7fe00b1c4d5` (shared empty `CowEnv`) fixed the outer allocation and its own doc
comment explicitly names *"a second `Arc<HashMap>` for `global_bindings`"* as
part of the ~600 B per binding it was accounting for — but it only shared the
`CowEnv`, leaving the inner map allocating per frame. Same mechanism, one level
down. This is exactly the "sweep the class, not the instance" case.

## Fix

`CowEnv::shared_empty_global_bindings()` — a thread-local
`Arc<HashMap<String, (Arc<str>, String)>>` singleton, used at all four sites.

Semantics-preserving by construction: every mutation of `global_bindings`
already goes through `Arc::make_mut` (`bind_global`, `mark_local`,
`copy_global_bindings_to`), which clones a shared `Arc` before writing. An empty
map has no observable identity, so sharing one is unobservable.

## Evidence

`src/compiler_rust/compiler/tests/interpreter_shared_empty_global_bindings.rs`:

- 1,000 `CowEnv::new()` frames must all become holders of the one shared Arc
  (pre-fix the shared Arc gained zero holders), and must release it on drop.
- `with_base` and `from_map` frames share it too.
- **Value semantics guard:** a frame that actually calls `bind_global` copies on
  write — the shared empty map is still empty afterwards, and a sibling frame
  does not observe the writer's binding.

## Class sweep (standing rule 1)

`/usr/bin/grep -rn "Arc::new(HashMap::new())" src/compiler_rust/compiler/src/value.rs`
now returns zero hits; the four sites were the whole population in `CowEnv`.
Pinned by a `must_not_contain` row in
`scripts/check/check-perf-regression-tests.shs`, so a re-introduced per-frame
allocation fails the gate.
