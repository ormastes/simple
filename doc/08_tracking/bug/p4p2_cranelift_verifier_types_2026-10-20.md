# Cranelift AOT "Verifier errors" in 7 phase-4 tool units (2026-10-20)

- **Status:** fixed in source (branch `work/p4p2-cranelift-verifier`); takes
  effect only after a producer rebuild. Not yet verified end-to-end.
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
| A1 | `call fnN(vX): arg 0 (vX) has type f64, expected i64` | special (via A2), statistics, execution_metrics, main_lazy_ctx_tools (`ln_f64`) | `cl_translate_call` declares every callee missing from `func_handles` (all cross-module calls) with an all-i64 signature, but the callee is defined with F64 params (`sig_type_to_cl`). | `cl_fallback_call_signature`: params from operand types, return from the dest local type; floats keep F32/F64 (`cl_fallback_abi_type`). |
| A2 | same text, in `gamma_fn` (`x.to_i64()` on `x: f64`) | special, statistics | `method_calls_literals.spl` erased-receiver admission accepts a receiver whose `receiver.type_` is nil (entry-closure lowering), so `f64.to_i64()` became the TEXT builtin (`rt_string_new`/`rt_string_len`/`rt_string_to_int_lenient` on a raw double). LLVM accepted this silently and got it wrong: `2.0 == 2.0.to_i64().to_f64()` evaluated to `false` in an LLVM-built repro. | `local_is_proven_numeric_scalar` excludes proven numeric receivers, so the numeric Cast arm handles them. |
| B | `ireduce.i64 vN: arg 0 (vN) with type i64 failed to satisfy type set` | unicode_scalar (`codepoint as char`), external_text | `cl_translate_cast` reduced to `mir_type_to_cl(target)`, which maps Char to I64, so the IR reduced i64 to i64. | `cl_cast_narrow_int_type`: Char is reduced to I32 (as in LLVM), and 64-bit targets are passed through unchanged. |
| C | `return vN: arguments of return must match function signature` | gzip.crc (`crc32_finalize`/`crc32_chunked`/`crc32_verify`) | HIR: a function with untyped params bails out of `declared_callable_type` before `infer_untyped_return_type` runs, so its return type stays Unit while the body still runs `return <value>`. LLVM hides this with a backend patch (`core_codegen.spl` "Untyped fns lower to Unit"). | `declaration_lowering.spl`: an untyped-param function with a value return gets an `Any` return type (the dynamic return, same as the bootstrap route). |

Regression spec:
`test/01_unit/compiler/backend/cranelift_verifier_type_contract_spec.spl`.
It has not been run: the only local binary is the Rust seed, and it fails to
parse the stdlib.

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
