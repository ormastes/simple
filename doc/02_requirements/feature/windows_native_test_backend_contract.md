# Windows native test backend contract

Selected by the user as part of Windows Phase 2 LLVM and Cranelift native executable testing, and issue #2187 implementation.

- REQ-NATIVE-001: Explicit `--native-backend=llvm|cranelift` builds and directly executes the selected backend's executable. Without that option existing compile/native SMF behavior remains compatible.
- REQ-NATIVE-002: Selected backend survives worker dispatch. Unknown backends, unqualified coverage, missing or changing producer bytes, failed compilation, and zero assertions cannot become a passing interpreter/SMF fallback.
- REQ-NATIVE-003: Native execution uses private caches and artifacts bound to source path, producer, backend, and execution; legacy result-cache evidence is excluded. Parent 80-worker execution uses one compilation worker per child.
- REQ-NATIVE-004: Positive and deliberately failing native assertion fixtures produce correct nonzero counts through both backends. Admission of the producer and runtime remains an external bootstrap controller gate.

Traceability: unit `native_backend_contract_spec.spl` covers selection, compatibility, argument and dispatch contracts, rejection, and count parsing. Integration `test_runner_native_backend_spec.spl` requires actual emitted executables and assertion outcomes. Full compiler, interpreter, loader inventories and Windows parallel80 qualification remain pending producer availability.
