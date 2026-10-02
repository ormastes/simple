# Explicit native backend test execution

Issue: https://github.com/ormastes/simple/issues/2187

The release Windows Phase 2 goal requires LLVM and Cranelift test executables with actual assertions. Existing `compile` and `native` modes intentionally compile SMF; changing those defaults would break compatibility. The additive `--native-backend=llvm|cranelift` option selects the Native route and requests AOT compilation explicitly.

The option is stored in `TestOptions.native_backend`, defaulting to empty. Selection forces no result-cache reuse and nonempty test execution. Legacy result entries do not identify their backend or producing compiler and therefore cannot qualify AOT work. The execution cohort includes the selected backend.

The owner compiles the existing SPipe-preprocessed source using `native-build`, the selected backend, and `core-c-bootstrap`. Each execution receives a private cache and executable name incorporating a source-path digest, producer digest, backend, and execution timestamp. Short digests keep Windows paths bounded; caches never share mutable writers. Each individual compilation uses one internal worker, permitting a parent pool of 80 independent test workers without creating 80 times 80 workers.

`SIMPLE_BINARY` must explicitly select the producer. The existing binary-resolution owner resolves it; the existing no-shell file SHA-256 facade fingerprints its bytes before and after compilation. Missing or changing producer bytes fail the test. `SIMPLE_RUNTIME_PATH`, when supplied by the admitted producer's controller, is forwarded to native-build. Admission and frozen runtime authority remain the controller's responsibility; a fingerprint alone is not admission. Stub fallback is disabled.

The emitted executable is invoked directly through the existing resource-scope process owner. Compilation failure does not degrade to interpreter or SMF execution. Unknown backends fail visibly. Cranelift coverage is rejected until instrumentation is qualified; it never substitutes LLVM. Executables reporting zero passed and failed assertions fail. Existing assertion failure counts remain failures.

Parallel workers transport the selected option through the compiled CLI's `test` command with sequential execution, disabled result caches and sessions, and `--assert-ran`. Windows redirected-process support is owned by issue #2188 and a separate implementation lane.

Unit coverage checks parser selection, SMF compatibility, backend compilation arguments, child transport, invalid requests, and result count parsing. Integration coverage compiles and directly executes a positive fixture and a deliberately failing fixture using each backend. Product qualification requires the admitted self-hosted producer and the real Windows toolchain; Rust-seed execution is not qualifying evidence. Full compiler, interpreter, and loader inventories and 80-worker Windows execution remain release gates.
