# Cranelift sent an untyped raw integer comparison through the dynamic comparator

A native import-closure build failed while converting `nogc_async_mut/db/accel.spl` and `common/string_core.spl`. The flat AST declaration indices were valid in their owner arrays, but `module_decl_at` rejected them in its bounds check. The diagnostic trace showed count `2` for the facade and `98` for `string_core`; the corresponding raw index/count comparison reached Cranelift's `rt_native_cmp` fallback. Cranelift treated any pair that was not both statically known scalars as dynamic, so a typed `i64` compared with a call result whose MIR VReg type was absent went through a tagged-value comparator.

For raw i64 values `0` and `2`, and `1` and `98`, the low three bits of the second operand are the legacy inline-float tag. The C comparator consequently treated these raw counts as tagged floats. The bounds comparison could report an invalid result and `module_decl_at` returned `-1`, which then became a blank declaration tag in the flat-AST bridge. This is a compiler/runtime representation boundary: absent type metadata means unknown raw value, not `Any`.

Cranelift ordering now follows LLVM's `ordering_needs_dynamic_cmp` rule: it selects `rt_native_cmp` only when an operand is explicitly `Any` and neither side is proven numeric. Missing VReg type metadata stays on the raw ordered-comparison path. Text ordering still uses `rt_text_cmp_any`, floats keep native float comparisons, and source-level `Any` ordering keeps its dynamic runtime dispatch.

The focused codegen regression was run in the isolated worktree based on `32491995db35a7533b7ad7699e45204fe8b8b045`:

```text
cargo test --locked --offline -p simple-compiler --lib ordering -- --nocapture
14 passed; 0 failed; 4376 filtered out
```

The test lane emitted Cranelift objects from Simple source and checked that a partially typed `i64` versus call-result comparison does not reference `rt_native_cmp`, while `Any`, text, and f64 orderings retain their respective paths. It also directly checks explicit-Any versus missing-type dispatch. The process-tree watchdog recorded a 4,857,324 KiB peak RSS under its enforced 5,859,375 KiB cap; the test profile took 1m45s. `rustfmt --check` on both changed Rust files and `git diff --check` passed. This test run compiled the Rust crate test binary; it did not rebuild the Rust seed or claim native execution of the app probe.
