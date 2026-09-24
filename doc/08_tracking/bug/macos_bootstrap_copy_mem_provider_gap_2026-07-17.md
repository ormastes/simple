# macOS bootstrap Rust-hosted archive lacks `copy_mem`
## Closed 2026-09-16 — Status Resolved in source 2026-07-17; focused runtime suite 7/7, archive exports copy_mem

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status

Resolved in source and focused runtime verification on 2026-07-17. The broader
Stage 3/4 bootstrap remains open under its own provider-selection gate.

## Evidence

The corrected `main` sources were compiled with the fresh Stage 3 compiler and
the isolated cache under `build/native_probe/main_closure/cache-stage3`.
`build/native_probe/main_closure/logs/stage3-fixed2.log` ends with:

```text
Undefined symbols for architecture arm64:
  "_copy_mem", referenced from:
      _compiler_rust__lib__std__src__core__list__List_dot_reserve
```

`copy_mem` is implemented by the monolithic `runtime_native.c` and pure-Simple
`simple_core/core_memory.spl`, but the Rust-hosted archive currently exports
only `rt_memcpy` from `runtime_memory.c`. The failure is therefore provider
composition, not source lowering.

## Resolution

`runtime_memory.c` now gives the Rust-hosted memory component an ABI-compatible
`copy_mem` owner that forwards to `rt_memcpy`. The focused runtime suite passes
7/7, including guard-byte and returned-destination assertions, and the rebuilt
`libsimple_native_all.a` exports both `_copy_mem` and `_rt_memcpy`.

The cached Stage 3 link no longer reports `_copy_mem`. Its subsequent failure was a
separate invocation/provider-selection issue: the old Stage 3 driver selected
`target/bootstrap/deps/libsimple_runtime.a` instead of
`libsimple_native_all.a`, leaving 73 hosted compiler hooks unresolved. Resume
with the explicit bootstrap hosted-bundle selector when investigating that
separate historical provider-selection failure.

## 2026-09-21 current-main audit

Status remains **closed** for the missing `copy_mem` provider. Freshly fetched
`origin/main` was `e0dd873da1b`. Open PR #1207
(`fix(macOS): repair Stage 3 HIR ownership and bootstrap portability`, head
`6a7a22ddc37`) was also inspected; its outstanding Stage 3/runtime verification
does not reopen this independently repaired provider gap.

The repair landed in `2d5b22b2083` on 2026-07-17. That commit added
`copy_mem(dst, src, n)` to `src/runtime/runtime_memory.c`, forwarding to
`rt_memcpy` and preserving the destination-pointer return. It also added the
still-present `hosted_copy_mem_forwards_to_the_bounded_memory_copy_owner`
regression in `src/compiler_rust/runtime/tests/framebuffer_c_runtime.rs`.
That regression checks an offset destination, both guard bytes, copied bytes,
and the returned destination. The historical 7/7 result above was not rerun
in this audit; no Rust compiler fallback was used.

Current main retains matching pointer/pointer/byte-count calling conventions
in the hosted owner, the monolithic runtime owner, and the pure-Simple
`src/runtime/simple_core/core_memory.spl` wrapper. No SOSIX ABI or implementation
change was made. The existing
`test/01_unit/runtime/runtime_memory_owner_composition_test.shs` additionally
checks that hosted memory composition defines `copy_mem` exactly once; its
GNU `nm --defined-only` invocation was not treated as a macOS test.

A focused macOS `nm -g` inspection of the admitted native archive found one
defined `_copy_mem` and one defined `_rt_memcpy`:

```text
                 U _rt_memcpy
00000000000015b4 T _copy_mem
00000000000015b0 T _rt_memcpy
```

Archive:
`/Users/ormastes/simple-tmp/astra-stage3-hir/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority/libsimple_native_all.a`.
SHA-256: `9a441b53b9146a7d5263646577ae1b1c28adda256ea2b963bb44bd7c585e8fd7`.
This proves symbol availability in that archive, not successful final provider
selection, native execution, or full Stage 3 admission.

The database title, owner path, regression pointer, and stale description were
corrected to refer to the repaired `copy_mem` gap rather than conflate it with
the later 73-hook link failure. This audit changes tracking only, so there is
no runtime performance or memory-allocation change to assess. No new benchmark
or current-baseline failure is claimed.
