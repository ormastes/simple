# Rust Driver Stale Vtable Debug Hook

## Status

Fixed in source on 2026-07-17 by deleting the temporary driver hook after its
debug module had already been removed.

## Reproduction

The bounded test-runner override check reached the driver binary target and
failed at compile time:

```text
error[E0433]: could not find `vtable_c8_debug` in `codegen`
  --> src/compiler_rust/driver/src/main.rs:1031
```

The stale `SIMPLE_DEBUG_VTABLE_TEST` branch called
`simple_compiler::codegen::vtable_c8_debug::run()`, but no such module remained.

## Prevention

The normal `simple-driver` binary compile gate catches any future reference to
a removed debug module. Temporary diagnostic entry points must be removed in
the same change that removes their implementation.

Verification was not retried in this session because three bounded driver-test
attempts had already reached the repository's hard retry cap: one compile
timeout, one library-target link failure, and this binary-target compile error.
