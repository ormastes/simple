# Linux aarch64 Stage 2: text-to-i64 conversion preserves a text handle

- **Filed:** 2026-10-02
- **Status:** OPEN; Stage 2 sanity fails. The conversion defect is isolated; the generic compiler fix and native qualification remain pending.
- **Platform:** Linux `aarch64-unknown-linux-gnu`, Cranelift Stage 2 built with 20 jobs from release/1.0 base `1ffaf797bab` plus the diagnostic and candidate fix commits in PR #2191.
- **Impact:** The Stage 2 compiler links, but the `p2_add` frontend sanity build fails before admission. No Stage 2 full CLI, test runner, or compiler/interpreter/loader test result follows.

## Measured sequence

The cold HIR caller reads `SIMPLE_SCV_INVENTORY_GENERATION`, parses it as `i64`, and decodes the immutable SCV source inventory. The inventory digest check passes before the failing generation check.

1. At the caller, bounded diagnostic output recorded `raw='2' raw_len=1 parsed=2 admitted=2`. The 11-argument `cold_hir_typed_receipts_from_lowered_sources_v1` then returned `cold-hir-inventory-generation-mismatch`.
2. A diagnostic inside that callee recorded `expected=1018926449 actual=3` while its caller recorded `raw='3' parsed=3 admitted=3` and the same source inventory digest `a7d0b369ee9fae7e479609ce872b1d959eb2d37072ff7ce97b08e13b8e4ef3d2`. The expected scalar changed across the compiled call; the inventory field survived.
3. Commit `87f5140a88a` moved the generation gate before the long receipt call and used a separate two-scalar helper. Its focused interpreter unit test passed (`Results: 3 total, 3 passed, 0 failed`), but the compiled Stage 2 sanity still failed: the caller recorded `raw='5' parsed=5 admitted=5` and the helper returned a mismatch.
4. A direct GDB run of the rejected Stage 2 worker broke at the two-scalar helper. Its AArch64 parameters were `x0=33957329` (`0x20625d1`, a tagged heap handle) and `x1=5` (raw `i64`). The object behind `x0` had length 1 and byte `0x35` (`'5'`); `rt_enum_id(x0)=-1` and `rt_value_as_int(x0)=53`, the code point of `'5'`. Disassembly showed the helper compares `x1` with `x0` correctly. The compiled `inventory_generation_text.to_i64() ?? -1` expression left the original text handle in the expected-generation slot. Interpolation rendered that handle as `5`, concealing the type mismatch.

The repair candidate mirrors the LLVM seed's already-established dynamic conversion route in both Cranelift method-call lowering paths. `rt_to_int_dynamic` parses registry-validated text and preserves a genuine integer receiver. A dedicated native probe passes an optional text value through `.to_i64() ?? -1` into an `i64` function and checks the numeric identity case. Native qualification is pending.

The Stage 2 binary was rejected on each attempt. The last attempt rebuilt 1,118 modules with 0 reused, linked, and exited with Stage 2 sanity status 2. The bounded three-cycle verify/fix limit has been reached; no fourth build was started.

## Evidence

- Caller diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-diagnostic.log`
- Callee diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-callee-diagnostic.log`
- Candidate fix run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-fix-final.log`
- Focused sanity receipt and log: `/dev/shm/simple-release10-phase2-20261002/output/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env` and `stage2-sanity.env.frontend-bootstrap-0.log` (latest run; earlier versions preserved under the bootstrap attempt archive)
- Focused unit log: `/dev/shm/simple-release10-phase2-20261002/logs/cold-hir-focused-unit.log`
- Rejected executable: `/dev/shm/simple-release10-phase2-20261002/output/stage2/aarch64-unknown-linux-gnu/simple.rejected`
- Direct worker breakpoint and register trace: `/dev/shm/simple-release10-phase2-20261002/logs/gdb-direct-worker.log`; worker argv and environment were captured from the canonical sanity process in `captured-worker-argv.bin` and `captured-worker-env.bin` in the same directory.
- A canonical-text generation check was prototyped and its interpreter unit specification passed (`Results: 3 total, 3 passed, 0 failed`), then removed from the source candidate in favor of the general codegen repair. The diagnostic log is `/dev/shm/simple-release10-phase2-20261002/logs/cold-hir-canonical-text-unit.log`.

## Next repair session

Add a native regression in which a typed text variable receives `.to_i64()` and is passed to an `i64` function; fix the MIR conversion lowering so the call receives raw `i64`. Keep the generation, inventory digest, and frozen snapshot checks intact. Rebuild from the current release head with separate caches and rerun the canonical Stage 2 admission; the interpreter unit PASS alone is insufficient for release.
