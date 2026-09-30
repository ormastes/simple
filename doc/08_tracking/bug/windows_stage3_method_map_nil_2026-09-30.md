# Windows Stage3 method map loses copied symbol identity

Status: source fix prepared; corrected native producer qualification pending.

Producer SHA256 `153006e6b78431cbed3fef502c5ccf726e3b40959c4e29c4e04147284c2143ac`, built from f9bdea7b3238bf8f791436d813b16cf7cd81c62f, parsed all 1018 source modules and crashed during HIR module 4 (`compiler.common.driver_compile_options`). Worker 21128 exited `3221225477` (`0xC0000005`); owned child cleanup succeeded. No Stage3 candidate or Stage4 PASS exists.

Windows dump `C:/Users/ormas/AppData/Local/CrashDumps/simple.exe.21128.dmp` records fault RVA `0x1b1960`: tagged value 3 (nil) is masked to zero and dereferenced at offset `0x50`. Adjacent strings `structclassconstantnametypemutablevolatilefixed-addressnone` identify the `hir_abi_interface_parts_v1` collection traversal. This matches the Linux method accumulator defect: native copies of struct `SymbolId` keys do not retain lookup identity, so the method merge inserts nil into the final function map.

A separate native reproducer containing two classes with static methods fails with the same access violation during its only module's HIR pass, after 49 ms, using the exact producer and runtime above. Evidence lives in `D:/dev/simple-windows-method-map-repro-20260930/baseline.result.json`; the fixture is `test/fixtures/method_symbol_identity/method_survival_probe.spl`. This is a failing baseline, not a regression PASS.

The fix keys the internal method accumulator by scalar `SymbolId.id`, then publishes each real function under its own authoritative `method.symbol`. It preserves methods rather than skipping nil values. Class methods, explicit impls and concrete trait defaults use the same representation. The source bundle also includes the reviewed imported-enum identity lifecycle, nested generic callable type-dependency traversal, and SOSIX facade routing fixes already prepared for Linux. Their executable regressions accompany this change; the method, enum and generic native tests require the newly rebuilt producer.

The previous f9b source, producer1530, Phase2 output, Phase3 cache and terminal receipts remain preserved. The next Windows producer uses a separate frozen source and ordinary cache directories, followed immediately by Phase3 and Phase4 diagnostic overlap as each complete compiler becomes available. Admission and sanity evidence remain independent.
