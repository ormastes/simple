# Bug: seed interp regression — d312b8e4253 (defer lazy imports) breaks module-global arrays in the native-build lane

- **Date:** 2026-07-24
- **Severity:** P0 — seed `native-build --backend llvm` (self-hosted .spl pipeline, interpreted) cannot parse ANY project; blocks the NVMe rv32 fw gate and every seed-driven cross build
- **Status:** ROOT-CAUSED by bisect; workaround active (seed built at `906b85d1420`); Rust-side fix pending

## Symptom

`src/compiler_rust/target/bootstrap/simple native-build --backend llvm --target riscv32-unknown-none ...`
dies while parsing the FIRST source file:

```
error: semantic: array index out of bounds: index is 3 but length is 0
```

Debug hook (`SIMPLE_INTERP_OOB_DEBUG=1`, added to
`compiler/src/interpreter/expr/collections.rs`) shows the failing access is
`expr_tag[eid]` — the AST expr pool (`src/compiler/10.frontend/core/_AstExpr/nodes.spl:84`)
reads as **empty** in the frame doing the read, while the parser has already
allocated eid 3. Backtrace confirms the whole run is
`run_file_interpreted_with_args` (pure interp — no JIT, no hybrid).

`SIMPLE_BOOTSTRAP=1` does NOT help: the env-mirror compat layer only covers
`expr_get_*` accessor reads; direct `expr_tag[eid]` array reads
(`module_state.spl:547`, `placeholder_lambda.spl:97,260,372`) bypass it.

## Bisect (seed tree only, driver rebuilt per point, same WC .spl sources)

| seed commit | result |
|---|---|
| `906b85d1420~1` | GOOD — 75 files parse in 120 s |
| `906b85d1420` (interp root fixes) | GOOD — 46 files parse in 60 s |
| `d312b8e4253` fix(bootstrap): defer lazy imports until first use | **BAD** — file 1: `class Span has no field named col` |
| `fdf03805bea` preserve flattened module global ownership | BAD — file 1: expr_tag OOB |
| `9cfb9e15d56` preserve module globals through method calls | BAD (= HEAD behavior) — file 1: expr_tag OOB |

First bad: **`d312b8e4253`**. The two follow-up "preserve module globals"
commits changed the symptom (Span field resolution → empty pool arrays) but did
not restore correctness: deferred lazy imports leave the importing module with
a fresh/empty instance of the owner module's globals instead of the shared one.

## Exonerated red herrings (this session)

- JIT `RUNTIME_SYMBOL_NAMES` registration: the run never JITs — registration
  can't affect it. (Separately real: bulk-registering 371 names the runtime
  does NOT export was wrong and got pruned back to 15 nm-verified exports;
  registering non-exported names seeds interp `EXTERN_FUNCTIONS` and hijacks
  same-named calls — the documented `rt_array_len_safe` class.)
- `rt_string_contains`: codegen-level alias (LLVM maps it to `rt_contains`),
  never a runtime export — must NOT be in `RUNTIME_SYMBOL_NAMES`.

## Workaround (active)

Build the seed driver with the tree at `906b85d1420`:
```
git checkout 906b85d1420 -- src/compiler_rust
cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver --features llvm
git checkout HEAD -- src/compiler_rust   # restore sources
```

## Fix requirements

1. Rust seed: make deferred lazy imports bind the importing module to the owner
   module's global storage (alias, not copy) — or defer only resolution, not
   storage identity.
2. Regression test: seed-interp cross-module module-var array write→read
   (writer module + reader module via re-export), mirroring
   `interpreter_flattened_module_globals.rs` but with deferred lazy imports on.
3. Gate: `check-nvme-rv32-minimal-live.shs` green on a seed built from HEAD.
