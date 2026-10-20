# Cranelift AOT "Verifier errors" in 7 phase-4 tool units (2026-10-20)

- **Status:** fixed in source (branch `work/p4p2-cranelift-verifier`); takes
  effect only after a producer rebuild. A1 verified end to end at the
  adapter level (two Cranelift objects linked and run, see below); the full
  phase-4 tool build has not been re-run.
- **Lane:** Phase-4 tool build, `native-build --backend cranelift`, entry
  `src/app/mcp/main.spl`, producer
  `p4-phase2-20261020/producer7-cl/simple-producer7-cl.exe` (release_phase3
  `87b9c74ff39` + Rust Cranelift bridge). The same modules build with LLVM.
- **Failing units:** app.mcp.main_lazy_ctx_tools,
  lib.common.encoding.external_text, lib.common.encoding.unicode_scalar,
  lib.common.math.special, lib.common.math.statistics,
  lib.common.perf.execution_metrics, lib.nogc_sync_mut.compression.gzip.crc.

## Getting the verifier text

The verifier text goes to worker stderr, and native-build drops it from the
middle of the stream. The full stream is saved by
`[native-build] FULL stderr (...) saved to: $TMP/native-build-stderr-*.log`,
and the `cranelift: AOT define_function error:` blocks appear in the
combined log in the same order as the `[native-compile-failed]` lines.
`compile_module` stops at the first function that fails, so each unit reports
only one function.

## Clusters, causes and fixes

| Cluster | Verifier text | Units | Root cause | Fix |
|---|---|---|---|---|
| A1 | `call fnN(vX): arg 0 (vX) has type f64, expected i64` | special (via A2), statistics, execution_metrics, main_lazy_ctx_tools (`ln_f64`) | `cl_translate_call` declares every callee missing from `func_handles` (all cross-module calls) with an all-i64 signature, but the callee is defined with F64 params (`sig_type_to_cl`). | Import signature from the CALLEE's declaration: MIR records the declared param types on the call operand (`MirSignature.declared_params`, from the callee symbol or the cross-module prescan registry; legacy `params` stay empty so LLVM is unchanged), and `cl_import_call_signature` builds the import from them. `cl_import_call_abi_error` rejects (`E-BACKEND-CRANELIFT-CALL-ABI`) any caller/callee register-class mismatch and any float crossing an unknown signature. No implicit coercion. (The first revision built the signature from the caller's operands: a silent miscompile, see below.) |
| A2 | same text, in `gamma_fn` (`x.to_i64()` on `x: f64`) | special, statistics | `method_calls_literals.spl` erased-receiver admission accepts a receiver whose `receiver.type_` is nil (entry-closure lowering), so `f64.to_i64()` became the TEXT builtin (`rt_string_new`/`rt_string_len`/`rt_string_to_int_lenient` on a raw double). LLVM accepted this silently and got it wrong: `2.0 == 2.0.to_i64().to_f64()` evaluated to `false` in an LLVM-built repro. | `local_is_proven_numeric_scalar` excludes proven numeric receivers, so the numeric Cast arm handles them. |
| B | `ireduce.i64 vN: arg 0 (vN) with type i64 failed to satisfy type set` | unicode_scalar (`codepoint as char`), external_text | `cl_translate_cast` reduced to `mir_type_to_cl(target)`, which maps Char to I64, so the IR reduced i64 to i64. | `cl_cast_narrow_int_type`: Char is reduced to I32 (as in LLVM), and 64-bit targets are passed through unchanged. |
| C | `return vN: arguments of return must match function signature` | gzip.crc (`crc32_finalize`/`crc32_chunked`/`crc32_verify`) | HIR: a function with untyped params bails out of `declared_callable_type` before `infer_untyped_return_type` runs, so its return type stays Unit while the body still runs `return <value>`. LLVM hides this with a backend patch (`core_codegen.spl` "Untyped fns lower to Unit"). | `declaration_lowering.spl`: an untyped-param function with a value return gets an `Any` return type (the dynamic return, same as the bootstrap route). |

Regression specs (run with the aarch64 Rust seed interpreting the compiler
source, 2026-10-20):
- `test/01_unit/compiler/backend/cranelift_verifier_type_contract_spec.spl` -- 10/10.
- `test/02_integration/compiler/backend/cranelift_cross_module_call_abi_spec.spl` -- 1/1;
  fixture `test/fixtures/compiler/cranelift_cross_module_call_abi/` builds a provider
  and a caller module with the Cranelift adapter, links them with a C harness and runs it.

## A1 cross-module call ABI: red / green (aarch64, two Cranelift objects + C harness)

| case | callee | first revision (caller-derived import) | fixed |
|---|---|---|---|
| `cv_take(2.0)` | untyped `fn cv_take(x)` | `cv=1` (garbage) | compile error: callee signature unknown, arg 0 is f64 |
| `cv_take_i64(2.0)` | `(i64) -> i64` | `cv=2` (garbage; expected reject) | compile error: arg 0 is f64 but the callee declares i64 |
| `cv_half_f64(3)` | `(f64) -> f64` | `cv=0.000` (garbage) | compile error: arg 0 is i64 but the callee declares f64 |
| `cv_half_f64(3.0)` | `(f64) -> f64` | `cv=1.500` | `cv=1.500` |
| `cv_take_i64(41)` | `(i64) -> i64` | `cv=42` | `cv=42` |

Calls whose callee signature MIR cannot recover (method calls, untyped
callees) keep the historical all-i64 import and now fail loudly on any float
value instead of passing it in the wrong register class.

## Workaround

`src/lib/nogc_sync_mut/compression/gzip/crc.spl` gets explicit parameter and
return types (`@workaround bug=p4p2_cranelift_verifier_types_2026-10-20`).
This clears cluster C for the current producer. Clusters A and B have no
practical source-level workaround: no spelling of a cross-module f64 call or
of `as char` avoids them.

## Repro evidence (producer7-cl, `--threads 4`, entry `src/app/zz_clver/main.spl`, not committed)

- Before: r1 (crc + unicode_scalar) gave `ERROR=2`. r2 (all 6 lib units plus
  crc probes) failed 9 units, and each failure matched one cluster above.
  r4/r5 narrowed special to `gamma_fn` (A2) and main to cross-module f64
  calls (A1). A typed-param copy of `crc32_finalize` (`-> i64`) built.
- After the crc workaround: r6 builds (`exit=0`), and the gzip.crc unit
  compiles under Cranelift.
- Separate, NOT a verifier issue: the crc repro binary SEGVs before its first
  `print` under BOTH Cranelift (r7) and LLVM (l2), while a hello-world
  Cranelift build runs. This is a runtime crash in the crc32 import path. It
  is not investigated here.
