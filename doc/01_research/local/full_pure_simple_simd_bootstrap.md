<!-- codex-research -->
# Full Pure-Simple SIMD Bootstrap: Local Research

Date: 2026-09-07

## Scope and method

This document reconciles current compiler, runtime, library, application, test, documentation, bootstrap, and deployment state for the combined portable-SIMD/database/web/Stage-4 lane. Three read-only sidecars inspected compiler SIMD, database/web portability, and bootstrap/docs/domain state. The shared checkout is heavily dirty; the files listed as dirty below remain unowned by this lane until an explicit integration manifest accepts them.

The feature has no exact route in `doc/00_llm_process/knowledge_registry.sdn`. `.spipe/full-pure-simple-simd-bootstrap/knowledge_selection.sdn` records the longest-prefix compiler, processing, library, app, tooling, and verification routes and the missing feature-route gap.

## Current SIMD implementation

The pure-Simple compiler already has a substantial SIMD pipeline:

- `src/compiler/30.types/simd_platform.spl` and `simd_capabilities.spl` model target/capability information.
- `src/compiler/35.semantics/simd_check.spl` validates SIMD language use.
- `src/compiler/50.mir/intrinsics.spl` defines MIR intrinsics.
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_provider.spl`, `auto_vectorize_codegen.spl`, `simd_recipe_infra.spl`, and `masked_simd_op.spl` provide optimization transforms.
- `src/compiler/70.backend/backend/native/` owns native lowering. The AVX-512 facade and `_X8664Avx512/{evex_encoding,mask_permute_ops,register_names}.spl` are substantive. Existing NEON and x86 SSE/AVX/AVX2 paths are present.

Coverage is not complete. `encode_rvv_zvk.spl` covers crypto-vector encoding rather than a general RISC-V V backend. General SVE/SVE2 and RVV backend files described by existing design documents were not found. Existing architecture and rollout documents therefore remain partly aspirational.

The Rust `simple-simd` detector exposes Scalar, SSE2, AVX2, AVX512, NEON, SVE, SVE2, RVV, and Wasm128 tiers. Dirty changes select AVX512 rather than downgrading it. Runtime kernels still map SVE/SVE2 to NEON and RVV/Wasm to scalar in important paths, so tier names do not prove native implementation.

Relevant uncommitted work currently includes:

- `src/compiler_rust/simd/src/{detection,host_config}.rs`
- `src/compiler_rust/runtime/src/value/{byte_kernels,collections,numeric_kernels,primitive_sort,utf8_kernels}.rs`
- `src/lib/common/simd_lane_pure.spl`
- `test/01_unit/lib/common/spec/simd_lane_512_spec.spl`

The Rust runtime changes add real x86 AVX-512 numeric, byte-search, ASCII/UTF-8, and byte-sort kernels with per-kernel feature checks and narrower fallbacks. The pure-Simple file adds architecture-neutral 512-bit scalar reference semantics. This is useful oracle work but does not satisfy a pure-Simple production implementation: the new executing kernels remain in Rust, and the pure-Simple reference says no `rt_simd_*` 512-bit twin exists.

Existing `runtime_simd_*.c` files are another platform boundary and mostly top out at AVX2/NEON or scalar-backed dispatch. A final design must separate the bootstrap/runtime substrate from the production pure-Simple API and prove which lower boundary, if any, remains unavoidable.

## Database state

The canonical pure SQL implementation is `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl` with `row_value_helpers.spl`. `src/lib/nogc_sync_mut/database/postgres_mimic/server.spl` composes PostgreSQL-like semantics but explicitly leaves wire framing to a later adapter, so it is not a complete pgwire network server. Generic transport exists at `database/server/transport.spl` over the standard TCP facade.

`src/lib/nogc_sync_mut/db/accel.spl` detects a SIMD tier and width but hardcodes `simd_active: false`. Equality, prefix, contains, delimiter, hash, bitmap, and related loops remain scalar. `database/query.spl` routes multi-filter work through bitmap acceleration only when that disabled flag is active. `test/05_perf/bench/simple_db_shared_accel.spl` explicitly benchmarks scalar fallback today.

High-value portable kernels are byte-span equality/prefix/delimiter, bitmap AND/OR/popcount, text scan/hash, typed-column scans, row encoding/decoding, filtering, and vector dot/L2 distance. Ordering, integer overflow, floating-point reduction order, and scalar tail behavior must remain specified.

`database/fast_db.spl` and `database/sql/connection.spl` are foreign adapters and must not become the canonical pure-Simple path. Several database modules directly declare file/runtime externs even though PureDatabase already uses standard file/capability facades; these are portability gaps for the strict no-platform-dependency requirement.

## Web-server state

Pure parsing and serialization live in `src/lib/nogc_async_mut/http_server/parser.spl`, `shared.spl`, `response.spl`, and `src/lib/common/net/http_core.spl`. Request-line, header, chunk, body, query, routing, and encoding scans are candidate byte-SIMD paths. Routing in `nogc_async_mut/web_framework/router.spl` remains scalar.

Network/file/time behavior is mostly behind `IoDriver`, TCP, TLS, file, and time facades. Direct thread dependencies remain in `http_server/server.spl` and `worker_owner.spl`; they need a capability owner or a documented accepted lower boundary. `src/app/web/main.spl` shells out to `./bin/simple`, so it does not meet the cached-artifact production-wrapper contract.

Existing database/web system and performance fixtures are useful but incomplete. There is no joint scalar-versus-selected-SIMD equivalence matrix for empty, lane-boundary, unaligned, and adversarial inputs. Web benchmarks record throughput/latency but not consistently max RSS and selected SIMD identity. The pure DB microbenchmark skips part of its comparison path.

## Bootstrap and deployment state

Canonical production output is Stage 4 under `bin/release/<triple>/{simple,simple_mcp_server,simple_lsp_mcp_server}`. `scripts/bootstrap/resume-stage4-from-admitted.sh`, `scripts/bootstrap/stage4-tooling-matrix.shs`, and `doc/09_report/bootstrap_redeploy_recipe_2026-07-30.md` describe the current route. The clean full-cycle command is `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`; reuse of verified prior stages may use its `--deploy --full-cli` route.

The present Windows bootstrap state is not admitted. `doc/08_tracking/bug/bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md` records a failed native-symlink publication and pending transaction. Transaction markers remain, while `src/compiler_rust/target/bootstrap` is an ordinary Cargo output directory inconsistent with the immutable generation named by the transaction. No authoritative Stage 3/4, deploy, rollback, or performance receipt was found.

`scripts/bootstrap/run-phase1-local.shs` stops after Stage 2 and is known to recover then hit the same symlink privilege failure. Repeating it unchanged would violate the three-cycle/no-identical-command guard. `scripts/setup/deploy-local-temp-mcp.shs` is explicitly a temporary raw-source Phase-1 route and cannot prove production deployment.

## Verification inventory and gaps

Useful focused evidence includes the Simple SIMD unit spec, compiler checks, strict-emission/native-execution SIMD specs, DB integration/system specs, PostgreSQL mimic spec, HTTP server specs, and database/web benchmarks. Missing release evidence includes:

1. A single portable capability/API contract spanning compiler, library, DB, and web use.
2. Native general SVE/SVE2, RVV, and Wasm128 implementation rather than detection labels and fallback.
3. Exact scalar-oracle equivalence across widths, tails, alignment, adversarial bytes, and floating-point policy.
4. Database and web hot-path integration with measured benefit and RSS bounds.
5. A phase matrix for compiler/interpreter/MCP/SPipe/DevHub/Caret checks and all phase-admitted tests.
6. An admitted Stage 3 lineage, exact Stage 4 candidate, essential-tool markers, deployment/rollback receipt, and production MCP smoke/performance receipt.
7. Ownership resolution for relevant dirty files and isolation from unrelated deletions/migrations.

## Research conclusion

The repository has meaningful SIMD foundations and a real pure-Simple AVX-512 encoder, but the requested end state is not present. The immediate decision is whether to finish a focused x86-first pure-Simple production slice, a portable fixed-width slice, or the complete fixed-plus-scalable cross-target program. Requirement selection must precede design and implementation.

