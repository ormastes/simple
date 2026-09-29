# Redeploy-pending expected-behavior specs

These `.spl` files encode the EXPECTED (post-fix) behavior for the cert
redeploy-kit defects. Design docs: `doc/03_plan/cert/redeploy_kit/`.

They currently FAIL on the frozen deployed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`) because the fixes live in the
Rust seed (runtime + cranelift JIT) and require a bootstrap rebuild + redeploy.
For that reason they live here, NOT in the normal test suite — a
perpetually-red gate is not the goal.

After a rebuild + redeploy, each should produce the expected output documented
in its header comment:

| Spec | Expected stdout | Frozen-binary actual |
|------|-----------------|----------------------|
| `print_array_value_based.spl` | `[1, 2, 3]` / `[[1, 2], [3]]` / `[]` | `<array@0x...>` x3 |
| `closure_return_across_function_boundary.spl` | `105` | `<invalid-heap:0x69>` |
| `trait_default_method_inherited.spl` | `Yo` / `Good day` | SEGFAULT (exit 139) |
| `mixin_class_use.spl` | `15` / `Alice` | `<value:0x...>` / `0.0` |
| `mixin_struct_use.spl` | `15` / `Alice` | `error` / `0` + stderr diag |
| `nested_closure_capture.spl` | `36` | `0` |

Item 01 (`print_array_value_based`) additionally has Rust unit tests that pass
NOW: `cargo test -p simple-runtime --lib io_print`.
