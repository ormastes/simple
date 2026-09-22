# Native list comprehension silently became nil

Status: scoped Rust implementation and native regression verification PASS;
independent Astra review PASS. Pure-Simple integration and full Phase2 remain
separate parent gates. This is not a bootstrap/release readiness claim.

## Cause and fix

The Rust HIR dispatcher omitted `Expr::ListComprehension`. Native compilation
uses lenient HIR, whose wildcard returned Nil/ANY. Production
`app.devhub.version_manifest.render_version_manifest` therefore lost its
projection list. With imported `ThreadHandle.join() -> i64?` metadata, the
erased receiver could also resolve `.join()` to the unrelated optional-return
method and fail concatenation with the exact optional-Add diagnostic.

The new HIR owner lowers a typed result-array block, generator loop, optional
filter, and projection append. It restores shadowed names/type hints on success
and errors. It preserves input evaluation count, filter/projection ordering,
array/string/range element typing, and result element type. It rejects unsupported
patterns, tuple iterables, invalid filters and noninteger ranges explicitly.
Tuple patterns over arrays remain supported. No method-resolution heuristic,
runtime ABI, application source, or wire-layout change is included.

Design: `doc/05_design/compiler/native_list_comprehension_lowering.md`.
Cross-agent contract: `doc/03_plan/agent_tasks/native_list_comprehension_2026-09-23.md`.

## Immutable baseline and isolated verification

Worktree: `/Users/ormastes/simple-tmp/native-list-comprehension-20260923`.
Base: `91131f979318db787cd046df38e53fc9dcb3f59b`.
Baseline admitted Stage2 SHA256:
`0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
Baseline path is the P0 phase2 source-matched `compiler.snapshot`; recorded
runtime capsule uses the same compiler hash under `phase-runtime-capsules/stage2`.
Cargo target/home are private clones; no shared cache or deployed candidate was
written. Pinned LLVM 23/nightly helper identities are in `toolchain.sha256`.

One implementation verification cycle, not three retries:

| Check | Baseline | Fixed |
|---|---|---|
| General comprehension values and exact effect order | Executable exit 1 | Exit 0; exact stdout |
| Production manifest with two projections, render and reparse | Exit 2: missing projections | Exit 0; exact stdout |
| Imported optional-return ThreadHandle.join context | Exact optional-Add HIR failure | Exit 0; typed array join |
| Focused HIR tests | New structural/diagnostic tests | 11 passed |

The context fixture is a true reduced red/green reproduction. It does not prove
the full CLI closure is fixed; Phase2 must independently admit that claim.

## Resource and performance evidence

All receipts enforce a sampled process-tree cap of 5,859,375 KiB and report
observer errors 0 and quiescent 1. This is not a kernel hard-memory limit.

| Run | Wall time | Peak tree RSS KiB |
|---|---:|---:|
| Three baseline probes | 7.69 s | 257728 |
| Private focused Rust test build + 11 HIR tests | 120.77 s | 3466096 |
| Native provider fixture suite | 13.03 s outer; 12.29 s test | 569312 |

Native build/run details: general 1 compiled/0 cached, 2900/337 ms;
manifest 27/0, 5832/313 ms; imported-join context 2/0, 2589/314 ms.
No fixture failed. These are bounded functional measurements, **not** a perf
PASS or valid speedup comparison: baseline omitted the computation entirely.
The implementation introduces linear traversal and result storage, not per-item
environment snapshots or a second filter pass.

Retained evidence under `build/native_probe/list-comprehension/`:
`baseline.log`, individual baseline build/stdout/stderr files,
`unit-cycle1.log`, `native-cycle1.log`, their `*-rss.env` receipts,
`provider-native/` executables/output/cache, `green.sha256`, `providers.sha256`,
`toolchain.sha256`, and exact launcher scripts. Native executable hashes:

- General: `6fe534908dc1ebe53a6d8fcc725895d1fddef3f8f16854b6d902df7fa9e40d75`.
- Manifest: `020d2814c153c08f8def500f642de17708dc716dba27153d59e42ec52ddf0b01`.
- Imported join: `45b5b9dde8122827f01b072c52d3dd5117129d673ff32e351cd3a1a130e1c3f4`.

## Review and remaining boundaries

Independent `/root/bootstrap_native_sampler/comprehension_astra_design` reviewed
the implementation, tests and recorded evidence: scoped STATUS: PASS with no
blocking findings. It did not rerun already-green checks. Working direct-env
audit passed; `doc/06_spec` contained zero executable `_spec.spl` files.

Rust interpreter filter/projection ordering remains a separately documented bug
(`list_comprehension_interpreter_filter_order_2026-09-23.md`). Pure-Simple
comprehension work belongs to its dedicated sidecar. Broader compiler/library,
MCP/LSP, full Phase2, bootstrap, and release checks were not run here, as the
parent explicitly restricted this lane to focused compiler/provider checks.
No full CLI/bootstrap build or push was performed.
