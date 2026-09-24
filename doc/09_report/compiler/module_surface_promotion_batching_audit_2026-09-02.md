# Module-Surface Promotion Batching Audit

Date: 2026-09-02

## Verdict

**STRUCTURAL PASS; SELF-HOSTED SPIPE BLOCKED.**

The optimization is implemented in Pure-Simple. The module-surface path performs
one transient-heap promotion per batch, retains every required owner, shallow-
frees only the temporary root carrier, and has no production bypass. No batching
implementation was added to the Rust seed runtime or interpreter.

## Ownership and lifetime

- The active transient scope remains the canonical mutable owner until pause.
- `module_surface_promote` builds one local `[Any]` carrier with 23 explicit
  retained child owners plus the `ModuleSurface` owner.
- `module_surfaces_promote` builds one local `[Any]` carrier with all 24
  freeze-time route owners per surface plus the registry owner.
- `module_surface_promote_roots` calls `rt_transient_heap_promote(roots)` once,
  then calls shallow `rt_array_free(roots)` once on both success and refusal.
- Shallow release cannot reclaim promoted children: the runtime ABI explicitly
  preserves element handles, the C scope end checks registry membership before
  dereferencing tracked entries, and the Rust runtime removes reachable objects
  from the scope before the carrier is unregistered. The simple-core capsule
  conservatively retains the whole promoted scope.
- Promotion refusal is also safe: only the carrier is shallow-freed, and the
  still-owned children remain eligible for normal scope-end reclamation.

## Bypass audit

The only production call sites are:

- `src/compiler/80.driver/driver_source_pipeline_parsing.spl:366` for one
  per-file surface batch.
- `src/compiler/80.driver/driver_source_pipeline_parsing.spl:510` for one final
  registry batch.

There is no direct `rt_transient_heap_promote(surface)` or
`rt_transient_heap_promote(retained_surfaces)` path in the driver. The only
direct runtime call in the module-surface registry is the private batch helper.

## Rust-seed scope

`src/compiler_rust/runtime/src/value/collections.rs` and
`src/compiler_rust/compiler/src/interpreter_extern/memory.rs` have zero working-
tree diff and contain no module-surface batching API. Three unrelated Rust
parser/test files currently carry concurrent backend-relocation path edits;
this audit neither owns nor changes them.

## Focused evidence

The source gate passed:

```text
promotion_batch_source_gate=pass helper_calls=1 surface_roots=24 registry_roots=25 driver_calls=1/1 rust_seed_runtime_diff=0
```

`test/01_unit/compiler/driver/stage3_promotion_batch_contract_spec.spl` now
checks every per-file owner, every freeze-time route owner, exact one-call
delegation, unique production callers, pause/promote/end ordering, direct-bypass
absence, shallow-free ordering, and absence of a Rust-seed batching surface.

Focused `git diff --check` passed.

## Blocked executable evidence

- The admitted `bin/simple` rejects `test`, so the focused SPipe spec could not
  execute. No SPipe PASS is claimed.
- The core-C capsule check could not start because unrelated concurrent changes
  under `src/runtime/` trigger its fail-closed clean-source precondition. No
  runtime-capsule PASS is claimed.

## Performance conclusion

For a scope with `A` tracked allocations and `S` retained surfaces, the old
registry path induced up to `24S + 1` separate runtime promotions and repeated
scope scans. The new path performs one registry promotion over the union root,
reducing the caller-induced scan term from `O((24S + 1)A + sum(R))` to
`O(A + sum(R))`. This is a structural complexity result; a fresh admitted
Stage3 build is still required for before/after wall-time and RSS evidence.
