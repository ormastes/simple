# Stale-spec hunt wave 5 (2026-07-11) — seam exhausted; real bugs found (report-only)

Wave 5 scanned 27 failing specs after waves 1-4 de-staled 13 spec families. **Zero retargeting
wins remain** — everything left is a real bug, an unimplemented placeholder, or out-of-scope
infrastructure. The stale-assertion seam from the self-hosting transition is closed.

## Real bugs (spec untouched; needs owner action)

1. **import_warning_spec.spl** — test-logic bug in `analyze_import_warning()`: relative import
   paths (`./`, `../`) contain `/`, which triggers the warning path BEFORE the relative-path
   check, so relative-import assertions return false.
2. **packed_struct_bitfield_spec.spl** — asserts
   `examples/09_embedded/simple_os/src/drivers/null_block.spl` contains
   `@packed struct NullBlockStatusRegister`; the file no longer exists (verified deleted).
   Needs either example restoration or spec retarget by the embedded owner.
3. **baremetal_build_spec.spl** — checks `compile_to_llvm_ir_pure`, which exists nowhere;
   `CodegenTarget.Arm`/`Riscv32` DO exist. The bare-metal compile pipeline was never completed —
   unimplemented feature, not a stale test.
4. **custom_blocks_easy_api_spec.spl** — "strips common indentation" fails: real string-matching
   implementation issue in the easy-API block handling.

## Postponed (too large for a de-stale pass)

- **stats_command_spec.spl** (+ twin): 11 `check(true, "Manual test placeholder")` stubs — needs a
  real rewrite invoking `bin/simple stats` and asserting actual output (the 122e625d
  launcher-dispatch rewrite is the template).

## Out of scope here

- **rv32_multi_backend_boot_spec.spl** — `Module 'timing' does not export 'hybrid_sim'`
  (bootstrap/LLVM territory).
- **stats_bug_schema_spec.spl** — hangs on temp-script execution (timeout), imports resolve fine.
- **sanitizer_config_spec.spl** — references deleted `src/compiler_cpp/` era; needs a current
  sanitizer strategy decision, not a retarget.

Previously filed (waves 2-4, unchanged): multi_mode_test_runner (removed API),
net_connect_completion (`expect(x.?)` compares receiver not bool), http_baremetal (stale doc
assertion in riscv64 FPGA plan).
