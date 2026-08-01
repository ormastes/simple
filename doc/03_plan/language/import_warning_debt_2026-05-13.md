# Import Warning Debt - 2026-05-13

Generated after resolver cleanup using the rebuilt release CLI at
`bin/release/x86_64-unknown-linux-gnu/simple`.

## Current Evidence

- `simple check src/compiler`: exits 0 with warnings only, 18 unresolved-import warnings.
- `simple check src/lib`: exits 0 with warnings only, 94 unresolved-import warnings.
- Resolver regression coverage: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler module_resolver --lib` passes with 49 tests.
- Check CLI coverage: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-driver cli::check --lib` passes with 16 tests.

## Resolver Cleanup Already Covered

- Numbered compiler layers: `compiler.backend.native.*`, explicit `compiler.35.semantics.*`.
- Relative imports: `.`, `..`, `...`.
- Compiler-root legacy bare imports: `ast`, `hir_types`, `type_infer_types`.
- Compatibility aliases: `compiler_shared.interpreter.*`.
- Stdlib aliases: `std.lib.*`, `src.std.*`, `common.*`, `app.mcp_jj.*`.
- Target-as-module imports: legacy forms such as `import aes/utilities`.
- Escaped `mod_` module references resolve to `mod.spl`, covering header-gen public exports.
- Stale `std.linker.elf_parser` and bare `lexer` compiler imports were rewritten to existing compiler namespaces.
- Missing `compiler.semantics.lint.public_doc` source was restored and locked by its existing PDOC001 spec.
- Stale `super.impl` fix-rule import was rewritten to the supported current-directory relative import form.

## Remaining Compiler Warnings

| Import bucket | Count | Likely owner | Notes |
| --- | ---: | --- | --- |
| `compiler.core.hir.lowering` | 6 | compiler source cleanup | Existing HIR lowering lives under `20.hir/hir_lowering`; import path is a legacy facade that has no exact module. |
| `verification`, `verification.proofs` | 6 | compiler/tools verification | Used by `90.tools/verify`; likely needs a package facade or import rewrite. |
| `weaving.diagnostics` | 2 | MDSOC/weaving | `85.mdsoc/weaving` has `weaving_result.spl`; no `diagnostics.spl` found. |
| `compiler.core.mir.lowering` | 2 | compiler source cleanup | MIR lowering exists under `50.mir`; legacy facade has no exact module. |
| `app.build.watch` | 2 | driver/watch | No matching `app/build/watch.spl` found in compiler tree. |

## Remaining Lib Warnings

| Import bucket | Count | Likely owner | Notes |
| --- | ---: | --- | --- |
| `app.debug.coordinator` | 30 | runtime-family parity | `debug/coordinator.spl` exists only in `nogc_async_mut`; `gc_async_mut` and `nogc_sync_mut` import it. Do not hide with cross-family resolver fallback unless debug coordinator is intentionally shared. |
| `std.text_core` | 6 | common stdlib facade | No `text_core.spl` found under current roots. |
| `std.common.math3d.Vec`, `common.math3d.Vec` | 5 | common math3d source cleanup | Existing file is `common/math3d/vec.spl`; import uses capitalized `Vec`. |
| `crypto_utils`, `base64_utils` | 5 | common crypto source cleanup | Used by scrypt; no matching common module file found. |
| `std.gc_async_mut.io.event_loop`, `std.gc_async_mut.io.driver`, `std.gc_async_mut.http_client` | 5 | runtime-family parity | `nogc_async_mut/io/event_loop.spl` and `driver.spl` exist; gc equivalents do not. |
| `lib.common.security.types`, `lib.common.security.audit_log` | 6 | security facade/parity | Family security files exist, but no `src/lib/common/security` facade exists. |
| `hardware.riscv_common.core.riscv_formal` | 3 | hardware parity | No matching module found under checked lib roots. |
| `common.text_layout.font_renderer` | 3 | text layout parity | Family font renderer files exist; no common facade exists. |
| Other one-off buckets | 31 | local source cleanup | Examples: `set_bit`, `point_equals`, `node_insert_point`, `multi_hash`, `host.async_nogc_mut.io.fs`, `decode_field`, `bytes_to_string`, `app.test_cache_shared`. |

## Recommended Next Actions

1. For library parity work, add or generate missing family facades rather than extending resolver cross-family fallbacks.
2. For compiler source cleanup, prefer import rewrites or real facade modules over new resolver aliases unless an alias maps to an existing documented namespace.
3. Keep `simple check src/compiler` and `simple check src/lib` warning counts in this file and in `simple_language_production_audit_2026-05-13.md` synchronized after each cleanup pass.
