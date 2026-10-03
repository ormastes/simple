# Six compiled subsystem test products

The requested acceptance matrix contains LLVM and Cranelift versions of three
executables: compiler, interpreter and loader. Compiler includes core, HIR, MIR
and the remaining compiler scopes; those are not additional final products.

Discover source owners with:

```sh
sh scripts/bootstrap/compiler-subsystem-test-inventory.shs "$SOURCE_ROOT" > source-specs.tsv
```

This manifest binds each candidate spec file to its SHA-256. It reads the
authoritative unit, integration and system trees, including their `compiler_core`,
`compiler_shared` and `core` sibling roots, excludes fixture/vendor and
legacy mirror trees, and assigns each physical path once: loader first,
interpreter second, otherwise compiler. Repeated backend execution is not extra
source coverage. Suffix-based discovery does not prove that a file registers a
test, nor count generated or conditional cases.

Before running each produced executable, ask that exact binary to enumerate its
registered tests without executing callbacks. Keep its path/hash, provider
identity, raw enumeration and exit status. Execute the same registry afterward;
retain per-case pass/fail/skip and the actual executed count. Unknown or absent
enumeration is BLOCKED, not zero and not an inferred source-pattern count.
An advertised threshold such as 1,000 cases is unproved until binary-owned
enumeration and execution evidence establish it.

Existing `--native-backend=llvm|cranelift` runs build one executable per spec.
The existing test runner's `--list` scans source text. Neither currently supplies
the three aggregate executables with binary-owned registration. The managed
Phase 4 acceptance specs are three-case behavior probes, not full subsystem
suites. Keep those results separate from the six-product matrix.

Manager integration must schedule each product's build, enumeration and run as
dependent operations, while unrelated products continue after failure. Preserve
compatible frontend caches and use the user's current worker budget (40 backend
jobs per lane for the active Windows repair). Missing binaries block only their
dependent inventory/run operations; they do not become successful test rows.

`--mode dynload` controls aspect packaging, whereas `--backend-plugin` selects a
Simple backend provider exporting `simple_backend_plugin_v1`. An LLVM toolchain
DLL or a fallback single binary does not prove that provider was loaded. Report
actual loaded provider path/hash/identity, separately from test counts. C++ test
framework linkage must retain the Simple assertions and share the executable's
registered cases; merely linking a library cannot establish coverage.

This page defines the requested acceptance boundary and source inventory. It
does not claim the aggregate harness, enumeration, dynamic compiler providers,
or complete manager wiring already exists.
