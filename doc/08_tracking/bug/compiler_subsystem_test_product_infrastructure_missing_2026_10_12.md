# Current branch lacks the retained subsystem test-product infrastructure

- Bug ID: `compiler_subsystem_test_product_infrastructure_missing_2026_10_12`.
- Status: confirmed source gap; minimal dependency-bound repair under review.
- Owner: Phase2 native-test lane. Authoritative bug-DB reconciliation pending;
  no qualified database CLI was used.

The requested products are compiler/interpreter/loader crossed with LLVM and
Cranelift. Their qualification remains 0/6, with zero original full-product cases
executed in this lane. Successful diagnostic helper links are not these products.

The existing retained `C:/p3` source contains the real implementation chain:

1. `scripts/bootstrap/build-compiler-subsystem-test-product.shs`.
2. `src/app/compiler_subsystem_product_generator/main.spl` and
   `src/app/compiler_subsystem_main_verdict/main.spl`.
3. `scripts/bootstrap/render-compiler-subsystem-product.pl`, which emits the
   product main and per-owner registration modules.
4. `src/lib/nogc_sync_mut/spec.spl` aggregate-registry APIs and native build.
5. `scripts/bootstrap/run-compiler-subsystem-test-products.shs`, which checks
   runtime enumeration and execution ledgers.

Current committed source lacks those generator/adapter applications, scripts,
and aggregate-registry APIs. Root independently searched the current library
tree for the aggregate registry and inspected both spec owners: the retained
owner includes `aggregate_registry_begin` and `aggregate_registry_finish`; the
current owner does not. A new compiler built solely from current committed source
will not restore this test-product pipeline automatically.

The retained inventory has 4,275 source owners: 3,848 compiler, 188 interpreter,
239 loader. These are file-owner counts, not registered or executed test counts.
Only genuine executable enumeration can establish the latter. Builder provider
identity checks must continue matching the requested LLVM/Cranelift backend and
the actual builtin V2 provider receipt.

Repair must pin the retained tool/runtime sources, identify their dependencies,
review overlap with current std.spec behavior, and apply necessary changes
individually. Do not import the entire retained tree, invent a substitute test
framework, or infer test success from generator output. Qualification requires
non-vacuous native enumeration, case-ledger validation and execution using the
actual repaired producer. Existing failed attempts and caches stay preserved.
