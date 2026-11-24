# Windows self-hosted compiler overflows the 1 MiB default stack lowering a deep `or` chain

- **Date:** 2026-11-24  **Lane:** rb5 bootstrap, release/1.0.0 pin `0285176e3a7b`, x86_64-pc-windows-msvc
- **Symptom:** Phase 3 -> Phase 3 (P3 compiling the bootstrap CLI) ended `go-to-end: 115 failure(s) (mir=115)`:
  three MIR shard workers died (`CRASH in the MIR shard pool`, 114 modules swept), attributed to
  `lib.common.process.observation_v4`, `app.build.targets.action_identity`,
  `compiler.driver.cache.native_build_environment_identity`.
- **Repro (in-process, cdb):** `native-build --threads 1 --emit-object src/lib/common/process/observation_v4.spl`
  under cdb -> `Stack overflow - code c00000fd`; frames resolve (lld /MAP) to
  `MirLowering.lower_expr_impl+0x1a6` / `MirLowering.lower_expr+0xd83` while lowering statement 2 of
  `freeze_process_observation_cleanup_receipt_v4` (`observation_v4.spl:1023`), a ~40-term `or` chain.
- **Cause:** `msvc.spl build_args` emits no `/STACK:`, so lld-link's 1 MiB default applies
  (`SizeOfStackReserve: 1048576` on both P2 and P3). The seed-built P2 lowers the same function; the
  P2-built P3 has larger frames and overflows. Recursive `lower_expr` depth is proportional to chain length.
- **Workaround (W51):** relink P3 with `/STACK:67108864` (same objects); the module lowers in 17 s.
- **Fix:** `build_args` adds `/STACK:67108864` unless `extra_args` already carries one;
  `PeImagePolicy.default()` stack reserve raised to 64 MiB for the internal COFF linker.
- **Still open:** `lower_expr` recursion on long binary-operator chains is unbounded in the source;
  an iterative lowering of left-assoc chains would remove the dependence on stack size entirely.
- **Open gaps (review 2026-11-24):** the `extra_args` override check matches `/STACK:` exact-case only (lld-link also
  accepts `/stack:`, `-STACK:`; the explicit flag still wins because it is pushed last). The windows-gnu lane
  (`native_all_support.spl` `NATIVE_MINGW_STACK_RESERVE_BYTES`, 8 MiB) would recur the overflow for a mingw-built compiler.
