# Linux aarch64 Stage 2: text-to-i64 conversion preserves a text handle

- **Filed:** 2026-10-02
- **Status:** OPEN; the generic conversion and import repairs compile, but the Stage 2 sanity worker segfaults in `ast_reset`. Native qualification remains blocked.
- **Platform:** Linux `aarch64-unknown-linux-gnu`, Cranelift Stage 2 built with 20 jobs. PR #2191 merged the earlier diagnostic helper; draft PR #2209 carries the generic conversion and import repairs; PR #2221 merged the independent seed OS-branch repair into release/1.0.
- **Impact:** The Stage 2 compiler links, but the `p2_add` frontend sanity build fails before admission. No Stage 2 full CLI, test runner, or compiler/interpreter/loader test result follows.

## Measured sequence

The cold HIR caller reads `SIMPLE_SCV_INVENTORY_GENERATION`, parses it as `i64`, and decodes the immutable SCV source inventory. The inventory digest check passes before the failing generation check.

1. At the caller, bounded diagnostic output recorded `raw='2' raw_len=1 parsed=2 admitted=2`. The 11-argument `cold_hir_typed_receipts_from_lowered_sources_v1` then returned `cold-hir-inventory-generation-mismatch`.
2. A diagnostic inside that callee recorded `expected=1018926449 actual=3` while its caller recorded `raw='3' parsed=3 admitted=3` and the same source inventory digest `a7d0b369ee9fae7e479609ce872b1d959eb2d37072ff7ce97b08e13b8e4ef3d2`. The expected scalar changed across the compiled call; the inventory field survived.
3. Commit `87f5140a88a` moved the generation gate before the long receipt call and used a separate two-scalar helper. Its focused interpreter unit test passed (`Results: 3 total, 3 passed, 0 failed`), but the compiled Stage 2 sanity still failed: the caller recorded `raw='5' parsed=5 admitted=5` and the helper returned a mismatch.
4. A direct GDB run of the rejected Stage 2 worker broke at the two-scalar helper. Its AArch64 parameters were `x0=33957329` (`0x20625d1`, a tagged heap handle) and `x1=5` (raw `i64`). The object behind `x0` had length 1 and byte `0x35` (`'5'`); `rt_enum_id(x0)=-1` and `rt_value_as_int(x0)=53`, the code point of `'5'`. Disassembly showed the helper compares `x1` with `x0` correctly. The compiled `inventory_generation_text.to_i64() ?? -1` expression left the original text handle in the expected-generation slot. Interpolation rendered that handle as `5`, concealing the type mismatch.

The repair candidate mirrors the LLVM seed's already-established dynamic conversion route in both Cranelift method-call lowering paths. `rt_to_int_dynamic` parses registry-validated text and preserves a genuine integer receiver. A dedicated native probe passes an optional text value through `.to_i64() ?? -1` into an `i64` function and checks the numeric identity case. The probe has not yet produced a native PASS.

The first 20-job Stage 2 run with this candidate rebuilt the Rust seed successfully, then failed while compiling `font_atlas_subrect_pixels`: `missing runtime fn 'rt_to_int_dynamic'`. The SFFI signature was present, but Cranelift filters runtime imports to MIR-referenced names and codegen roots. The `.to_i64()` lowering synthesizes the runtime call after MIR reference collection. The follow-up repair adds `rt_to_int_dynamic` to `runtime_symbol_is_codegen_root` and asserts its retention in the focused codegen-root test.

The isolated one-job Rust unit invocation timed out after 240 seconds while compiling its test binary, before it printed a test result. This is not a PASS.

The second 20-job native attempt compiled the seed and runtime with the import repair, but stopped during source discovery before Cranelift codegen: `windows_redirected_process.spl` uses a module-level `@when(os="windows"):` block, and the Rust seed parser treated it as a function decorator (`expected Fn, found Colon`). A narrow Rust seed preprocessing step now selects the Windows body or its `@else` fallback before discovery parsing and preserves line numbers. The focused Rust parser test passed for Windows and Linux (`1 passed, 0 failed`).

The final 20-job attempt compiled 1,133 modules with zero failures and linked a 48,239 KB Stage 2 binary in 1,006.3 seconds. Its `p2_add` sanity worker then died by SIGSEGV before admission. The preserved core places the fault at `ast_reset+4580` during `CompilerDriver.parse_full_frontend_selected_v1`: the generated store targeted address zero because global `decl_nodes__module_path_slot` held a tagged array with length 1 and null data pointer. This occurs during parsing, before HIR traversal; the separate optional-HIR visitor repair in merged PR #2219 does not explain this crash. The three-cycle verify/fix cap is reached. No admitted Cranelift compiler or compiler/interpreter/loader matrix exists from this branch.

The Stage 2 binary was rejected on each attempt. No fourth build was started.

## Evidence

- Caller diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-diagnostic.log`
- Callee diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-callee-diagnostic.log`
- Candidate fix run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-fix-final.log`
- First generic conversion run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-erased-text-dynamic-20.log`; exact panic preserved in `/dev/shm/simple-release10-phase2-20261002/logs/stage2-native-build-missing-to-int-import.log`.
- Focused Rust unit compile attempt: `/dev/shm/simple-release10-phase2-20261002/logs/codegen-root-focused-test-isolated.log` (timeout, no test result).
- Second native attempt: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-erased-text-import-root-cycle2.log` (source discovery parse error, before codegen).
- OS branch parser test: `/dev/shm/simple-release10-phase2-20261002/logs/os-when-focused-rust-test-fixed.log` (`1 passed, 0 failed`).
- Final native attempt: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-os-when-final-cycle3.log`; rejected executable at `/dev/shm/simple-release10-phase2-20261002/output/stage2/aarch64-unknown-linux-gnu/simple.rejected`.
- Crash: `/var/crash/_dev_shm_simple-release10-phase2-20261002_output_stage2_aarch64-unknown-linux-gnu_simple.1000.crash`; bounded GDB traces `/dev/shm/simple-release10-phase2-20261002/logs/crash-cycle3-gdb.log` and `crash-cycle3-gdb-registers.log`.
- Focused sanity receipt and log: `/dev/shm/simple-release10-phase2-20261002/output/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env` and `stage2-sanity.env.frontend-bootstrap-0.log` (latest run; earlier versions preserved under the bootstrap attempt archive)
- Focused unit log: `/dev/shm/simple-release10-phase2-20261002/logs/cold-hir-focused-unit.log`
- Rejected executable: `/dev/shm/simple-release10-phase2-20261002/output/stage2/aarch64-unknown-linux-gnu/simple.rejected`
- Direct worker breakpoint and register trace: `/dev/shm/simple-release10-phase2-20261002/logs/gdb-direct-worker.log`; worker argv and environment were captured from the canonical sanity process in `captured-worker-argv.bin` and `captured-worker-env.bin` in the same directory.
- A canonical-text generation check was prototyped and its interpreter unit specification passed (`Results: 3 total, 3 passed, 0 failed`), then removed from the source candidate in favor of the general codegen repair. The diagnostic log is `/dev/shm/simple-release10-phase2-20261002/logs/cold-hir-canonical-text-unit.log`.

## Next repair session

Diagnose why `decl_nodes__module_path_slot` has length 1 with a null data pointer after `_ast_slots_ensure` in the Cranelift-built `ast_reset`. Qualify the generic text-to-i64 fix with the existing native probe only after Stage 2 admission, then build a Cranelift full CLI and test runner for compiler, interpreter, and loader suites. Preserve the generation, inventory digest, and frozen snapshot checks. The three-cycle cap for this session is exhausted.
