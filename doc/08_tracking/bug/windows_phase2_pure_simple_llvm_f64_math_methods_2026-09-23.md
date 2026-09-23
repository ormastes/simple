# Windows Phase 2: pure Simple LLVM cannot resolve `f64.sqrt` and `f64.abs` in database stats

- **Filed:** 2026-09-23
- **Status:** OPEN pending canonical Phase 2 test-runner build and execution on the repaired source
- **Source revision:** `8b131cbf1c64ebf9034700e4369a015777b35f45`
- **Producer:** admitted Stage 2 `simple.exe`, SHA-256 `bee5699df10d7ba1e54263e18c6f81a5b2c5165909711e83ecf4810cbe675c25`
- **Scope:** Windows `x86_64-pc-windows-msvc`, pure Simple LLVM native build, `SIMPLE_NO_STUB_FALLBACK=1`

## Reproduction and impact

The canonical Phase 2 verifier built the test runner from `src/app/test_runner_new/main.spl` with `--source src/compiler --source src/app --source src/lib --entry-closure`, 12 build threads, and the admitted Stage 2 producer. It failed before producing a test-runner binary. The preserved log is `D:/p2w8b/logs/test_runner_build.log`:

```text
FAILED FILES (1):
  - D:\b8bfresh\src\lib\nogc_sync_mut\database\stats.spl => ... llvm codegen: semantic: cannot resolve method call `f64.sqrt`: receiver is a builtin type but `sqrt` is neither a known runtime method nor a resolvable user definition (checked use_map/import_map for `sqrt`)
Build failed: native-build aborted: 1 file(s) failed to compile
```

The failing expression was `variance.sqrt()` in `src/lib/nogc_sync_mut/database/stats.spl:102` at that revision. An isolated no-stub native probe against the same producer then reached the identical `f64.sqrt` error in `src/lib/nogc_async_mut/database/stats.spl`. After replacing those calls, both modules exposed the next unsupported receiver method, `f64.abs`, in `is_significant_change`.

This is distinct from `float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`: that FIXED report covered Rust seed interpreter/JIT dispatch. Here the admitted pure Simple Stage 2 compiler's LLVM semantic path rejects two methods that the source uses.

## Repair and current evidence

Commit `e73e3832f6f` replaces both methods in both database-statistics copies with the existing pure Simple `std.common.math.special.{sqrt_f64, fabs}` functions. It adds an exact sample-standard-deviation unit case and synchronous/asynchronous native probes. The probes' final no-stub builds passed source compilation and reached linking, where the isolated environment lacked `gcc` for `_main_stub.c`; see `D:/wk-p2-f64-sqrt/build/native_probe/f64_sqrt/{sync,async}/build-final.log`.

Thus the focused evidence clears the original LLVM semantic errors but does not establish a linked executable, probe runtime PASS, or canonical Phase 2 PASS. The canonical test runner still needs to be rebuilt and run from the repaired source with its configured Windows toolchain. Do not mark this bug fixed from the isolated probes alone.
