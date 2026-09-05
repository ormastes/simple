# Rust seed native-build ignored its configured default backend

Status: source-fixed; staged execution pending (2026-07-19)

## Reproduction

`NativeBuildConfig::default()` selected LLVM when the seed was built with LLVM,
but native project compilation, cache identity, and linker helpers read only
`SIMPLE_BACKEND`. With no explicit environment override, they silently selected
Cranelift. A flagless “default LLVM” parity lane could therefore exercise
Cranelift twice.

## Fix

The builder resolves a valid explicit `SIMPLE_BACKEND` override once, otherwise
keeps `NativeBuildConfig.backend`. That resolved value is threaded through
parallel and sequential compilation and is reused by cache and linker paths.
LLVM remains the enabled-seed default; explicit Cranelift remains supported.

## Regression

`test_default_config_mangle` pins the feature-dependent config default, and the
compiler entrypoint now requires the selected backend as an argument instead of
rereading process environment. The existing strict parity runner supplies the
explicit Cranelift comparison lane.
