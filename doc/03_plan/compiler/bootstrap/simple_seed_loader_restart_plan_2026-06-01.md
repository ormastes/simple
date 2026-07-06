# Simple Seed Loader Restart Plan - 2026-06-01

## Goal

Resume the segfault/loader hardening work with Rust treated only as the seed/tooling binary. Fix the Simple implementation path first.

## Current State

- Default `bin/simple` had previously been confirmed as the deployed pure Simple bootstrap.
- Rust-side hardening exists from the interrupted parent thread, but it should be treated as seed/tooling guardrail work, not the main fix.
- Simple-side guard work was started in:
  - `src/compiler/70.backend/linker/lld_sffi.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_loader.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_target.spl`
  - `src/lib/nogc_sync_mut/sffi/llvm_types.spl`
  - `src/lib/log.spl`
  - `src/compiler/99.loader/loader/smf_mmap_native.spl`
  - `src/compiler/70.backend/linker/_SmfReaderMemory/header_parser.spl`
  - `src/compiler/70.backend/linker/_SmfReaderMemory/symbol_parser.spl`
  - `src/compiler/80.driver/smf_writer.spl`
  - `src/compiler/99.loader/loader/module_loader.spl`
  - `src/compiler/99.loader/module_loader.spl`
- Temporary debug files under `build/tmp/` were deleted before this restart note.

## Known Findings

- `test/01_unit/compiler/loader/module_loader_relocation_spec.spl` still fails.
- The failure is not resolved by the partial layout fixes yet.
- Diagnostic work indicated:
  - Simple SMF writer/reader layout assumptions were inconsistent.
  - The in-memory reader needed 64-byte section table entries.
  - The Simple writer symbol entry needed to align with the documented 56-byte symbol layout.
  - Header parsing in `_SmfReaderMemory/header_parser.spl` was reading offsets as if there were extra repr(C) padding, but `smf_header.spl::to_bytes()` writes packed fields.
  - The compatibility `compiler.loader` facade path can return a successful load with zero symbols.
  - A separate parse blocker exists in `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`: `Unexpected token: expected expression, found Else`.
- 2026-07-04 focused restart evidence:
  - High-bit byte writes through `file_write_bytes` now round-trip via the seed runtime.
  - SMF writer/reader DRVS round-trips pass the focused seed specs.
  - `LibSmfReader.get_module` currently skips the u64 module-hash comparison because Simple field/local copies truncate high hash bytes in this path; byte-exact file round-trip specs cover the corruption this guard was catching. Restore the hash guard after the u64 copy bug is fixed.
  - Math distribution NaN generation no longer uses semantic division by zero, and corrected distribution expectations pass.
  - `sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp` rebuilt the Rust seed/runtime and reached Stage 4 full CLI compile, but Stage 4 stayed silent and was stopped at the bounded cap before refreshing `bin/release/x86_64-unknown-linux-gnu/simple`.
  - Stage 4 now uses the documented direct `run src/app/cli/native_build_main.spl -- ...` seed fallback and reports Stage 3's missing executable accurately. A bounded 25-minute deploy retry showed the worker stayed CPU-active with diagnostics captured, but still produced no refreshed full CLI binary before timeout.
  - 2026-07-05 self-host evidence: an existing `bin/release/.../simple run src/app/cli/native_build_worker.spl ... --entry src/app/cli/main.spl` worker stayed CPU-bound for more than 1h33m, wrote no stdout, produced no `simple_selfhost` output, and left its `--cache-dir` empty. The Stage 4 blocker is before object/cache emission, not deploy copy or linker output.
  - 2026-07-05 parser evidence: `SIMPLE_COMPILER_TRACE=1 SIMPLE_INTERP_TRACE=1 bin/simple native-build ... --entry-closure --entry src/app/cli/main.spl` reached `phase2:parse:entry src/app/cli/_CliMain/args_and_os_commands.spl` but did not reach `entry:done` before the bounded timeout. A focused `bin/simple check src/app/cli/_CliMain/args_and_os_commands.spl` also timed out after 30s.
  - 2026-07-05 partial source cleanup: `args_and_os_commands.spl` had a self-cycle through `use app.cli.main.*`, stale dispatcher imports, duplicate inline SimpleOS command handling, and `std.log` in the hot parser path. The split now uses direct imports, the dispatcher calls existing `os.cli.handle_os`, and CLI error wrappers print directly. A focused `bin/simple check src/app/cli/_CliMain/args_and_os_commands.spl` still times out after 30s; redeploy remains blocked.
  - 2026-07-05 current retry: removing the `??` fallback, the unused stack-overflow flag marker, the inline `if` expression, and the wide `GlobalFlags(...)` return constructor did not clear the focused `bin/simple check --json src/app/cli/_CliMain/args_and_os_commands.spl` timeout after 90s. Keep those as source simplifications only if a narrower parser repro proves value; otherwise do not commit them as a redeploy unblocker.
  - 2026-07-05 bug tracker: remaining CLI global-flag parser/check timeout is filed at `doc/08_tracking/bug/cli_global_flags_check_timeout_2026-07-05.md`. Bounded `/tmp` slices pass through run-config handling, then time out when the backend option pair is added; continue from that minimal branch boundary instead of rerunning full bootstrap.

## Restart Steps

1. Inspect current diffs before editing; preserve unrelated dirty work.
2. Re-run focused lint on the Simple files touched above.
3. Decide whether the partial compatibility-loader changes in `src/compiler/99.loader/module_loader.spl` should be completed or reverted in favor of fixing the newer `src/compiler/99.loader/loader/module_loader.spl` path.
4. Fix the SMF layout contract in one place:
   - section table entry size
   - symbol entry size
   - symbol type/binding values
   - header byte offsets
   - string table offset calculation
5. Fix the compatibility loader returning success with zero symbols.
6. Re-run:
   - `src/compiler_rust/target/bootstrap/simple lint <focused Simple files> --json`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/loader/module_loader_relocation_spec.spl --mode=interpreter --clean`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/lib/log_lite_ring_spec.spl --mode=interpreter --clean`
7. Re-run the 2026-07-04 focused checks after any related edit:
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/linker/lib_smf_spec.spl --mode=interpreter --clean`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/linker/lib_smf_writer_spec.spl --mode=interpreter --clean`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/linker/file_byte_alias_spec.spl --mode=interpreter --clean`
   - `src/compiler_rust/target/bootstrap/simple test test/01_unit/lib/common/math/distributions_spec.spl --mode=interpreter --clean`
8. Get `sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp` past Stage 4 and confirm `bin/simple --version` resolves to the refreshed pure Simple deployed bootstrap.
9. Confirm `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Agent Refactor Handoff

Use `doc/03_plan/agent_tasks/bootstrap_compiler_interpreter_loader_arch_refactor.md`
for the broader bootstrap / compiler / interpreter / loader architecture lane.
This restart plan remains the bounded loader/bootstrap recovery checklist; do
not fold unrelated interpreter or compiler-layer refactors into this lane.

## Important Constraint

Do not continue expanding Rust fixes unless required for seed/tooling diagnostics. The product fix belongs in Simple code.
