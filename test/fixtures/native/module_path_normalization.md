# Production module-path native matrix

Compile module_path_normalization.spl via the Stage2 positional native-build
route, not --entry (which delegates to the bootstrap producer). It imports
the production compiler.common.module_path_naming module directly. Exit0 and
`module-path-normalization-26-pass` are both mandatory; output-only success or
the existence of an object is insufficient.

Recorded compiler arguments, from an isolated worktree:

```text
native-build --target aarch64-apple-darwin --backend cranelift
--runtime-bundle core-c-bootstrap --threads 1 --cache-dir <private-cache>
--mode dynload --runtime-path <frozen-runtime-authority>
-o <private-output> test/fixtures/native/module_path_normalization.spl
```

Both baseline and patched runs use the frozen rejected Stage2 only for the
explicit bootstrap-defect diagnostic, not as a generally admitted runtime.
Environment: SIMPLE_BINARY=<private-stage2>, SIMPLE_BOOTSTRAP=1,
SIMPLE_NO_DEPRECATED_WARNINGS=1, SIMPLE_STAGE3_STREAMING_SURFACES=1,
SIMPLE_FRONTEND_CACHE=0, SIMPLE_NATIVE_ARENA_DECLS=1,
SIMPLE_NO_STUB_FALLBACK=1, SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct,
SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE=none,
SIMPLE_NATIVE_BUILD_TARGET=aarch64-apple-darwin, SIMPLE_NATIVE_BUILD_THREADS=1,
SIMPLE_NATIVE_BUILD_CACHE_DIR=<private-cache>, SIMPLE_PACKAGE_INDEX_COLD_INIT=1,
SIMPLE_RUNTIME_PATH=<frozen-runtime-authority>,
SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap, SIMPLE_LIB=<worktree>/src.
LLVM23 environment is inherited from the frozen bootstrap authority.
Wrap compilation with process-tree-rss-watchdog.pl cap5859375 KiB/timeout180
and /usr/bin/time -l; runtime timeout30. Preserve every receipt and log.

Baseline: compile0, runtime24 with24 explicit mismatches. Patched cycle2:
objects emitted but capsule identity gate rejects; no compiler PASS claimed.
The parent-authorized independent diagnostic link uses those exact objects,
unmodified generated Stage2 main shim, and the separately admitted core-C
capsule/backfill. Link/run0 verifies all26 cases; it does not admit a capsule.

External link uses LLVM23 clang -fPIC -Wl,-dead_strip -Wl,-map,<map>, then the
entry shim, module object, fixture object, -Wl,-force_load,<canonical-core.a>,
and the real compiler-backfill archive. Remaining libraries/frameworks are
the exact already-qualified composition in
cranelift_module_symbols/QUALIFICATION.md. No trap member removal or stub
fallback is performed. The canonical capsule manifest already passed65 checks.

Exact paths, hashes, root-cause disassembly, timings, scope limits, and final
debugger-only compiler cycle are recorded in
doc/08_tracking/bug/stage2_module_path_predicate_tagging_2026-09-23.md.
No green check should be rerun merely to reconfirm it.
