# bootstrap_main selected the core-C runtime for compiler-provider imports

## Evidence

The fixed Rust-seed diagnostic compiled `bootstrap_main` without source errors,
then failed at link time with 82 unique undefined symbols.  The retained
inventory is
`build/mini_builds/phase4_tools_rust_seed/retry_dynamic_receiver_fixed/undefined-symbols.txt`.

## Root cause

`bootstrap_main` imports the native compiler provider ABI (`rt_cranelift_*` and
`rt_native_build`) in addition to ordinary runtime helpers.  The selected
`core-c-bootstrap` archive intentionally owns only the Simple/C core ABI.  It
must not grow hosted compiler stubs.  The diagnostic command omitted the
canonical Stage-3 `--runtime-path`, bypassing existing owners: compiler
backfill owns the 71 Cranelift exports, the narrow Rust runtime projection owns
10 general helpers, and `libsimple_native_all.a` alone owns `rt_native_build`.

## Gate and disposition

Run `scripts/check/check-bootstrap-main-provider-symbols.shs INVENTORY ARCHIVE...`
against the selected provider set before linking this diagnostic shard.
Production Stage 4 remains tools-only
and compiles zero compiler sources; this Rust provider selection is diagnostic
bootstrap evidence, not an admitted pure-Simple Stage-3 receipt or production
PASS.
