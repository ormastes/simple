# Pure-Simple JIT cannot link `rt_*` externs: the Cranelift provider registers no runtime symbols

- **Filed:** 2026-11-13
- **Status:** FIXED for the provider (2026-11-13, lane `work/jit-provider-runtime-symbols-20261113`): runtime externs link natively from the pure-Simple JIT. Limits remain; see "Not covered".
- **Related:** `jit_caret_392_unregistered_externs_hybrid_splice_2026-11-13.md` (the seed JIT's own 392-extern splice; a different code path with the same root shape)
- **Pinned by:** `test/01_unit/compiler/backend/jit_runtime_extern_native_link_spec.spl` (2/2, untagged), `jit_runtime_extern_interpreter_parity_spec.spl` (3/3), seed `cranelift_jit_runtime_symbols_tests.rs` (5/5)

## Summary

The pure-Simple compiler's JIT (`src/compiler/70.backend/backend/`) generates
code through the `rt_cranelift_*` provider. On every host that can run it, that
provider is the Rust seed's `cranelift_sffi.rs`. The provider binds imported
symbols by process symbol lookup only. It registers no runtime symbol table,
and the seed binary exports no `rt_*` symbol dynamically. So no `rt_*` extern
can be linked natively by the pure-Simple JIT, whatever the pure-Simple side
declares.

## Evidence (seed `simple-seed-v4`, aarch64 Linux, `origin/release/1.0.0` `26e2b8616bd`)

1. `rt_cranelift_new_module_impl` builds the module with
   `JITBuilder::with_isa(isa, cranelift_module::default_libcall_names())` and
   adds no symbols (`src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs`).
   `rt_cranelift_finalize_module` calls `finalize_definitions().unwrap()`.
2. `nm -D --defined-only <seed> | grep -c ' T rt_'` prints `0`.
3. A 25-line probe that declares one import, calls it from a JIT function and
   finalizes the module:

   | import | result |
   |---|---|
   | `getpid` (libc) | `finalize=1`, call returns a positive pid, exit 0 |
   | `rt_time_now_unix_micros` | host aborts at finalize, exit 134: `PANIC can't resolve symbol rt_time_now_unix_micros` |

   The abort is a Rust panic across an `extern "C"` boundary
   (`fatal runtime error: failed to initiate panic`). It is not an error value
   the caller can handle.

## What the pure-Simple side did before 2026-11-13

The kernel-facing JIT lane (`static_backend_cranelift_jit_lane.spl`) drove
`CodegenPipeline.jit()` in `src/compiler/70.backend/codegen.spl`. That pipeline
never reached extern resolution:

- `init_module` maps `CraneliftTarget.Native` to `CL_TARGET_X86_64`, and the
  provider refuses a JIT module whose architecture is not the host's. On aarch64
  every run answered `failed to initialize module`.
- A named callee (`Const(Str(name))`, Runtime or Foreign origin) fell to
  `compile_cranelift_const`'s default arm, `cranelift_iconst(I64, 0)`, and that
  value was passed to `cranelift_call` as a func-ref handle. No import was
  declared and no diagnostic named the extern.
- It calls `cranelift_begin_function` and `cranelift_get_function_ptr` with
  (ptr, len) name pairs, which the current `std.sffi.codegen` wrappers do not
  take.

Natively linked runtime externs before: 0. No module executed at all on this
host.

## What changed (lane `work/pure-simple-jit-externs-*-20261113`)

- `cranelift_jit_run_main` (`cranelift_codegen_adapter.spl`) lowers a MIR module
  with the lowering the AOT lane already uses, into a host JIT module, and calls
  `main`. The JIT lane now runs it. There is one call lowering for both lanes.
- `jit_extern_resolution.spl` classifies every named callee once per module by
  `MirOperand.call_origin`, before any code is generated:

  | Callee | Outcome |
  |---|---|
  | Source, defined in the module | local call |
  | Foreign | import, bound natively by the provider |
  | Runtime (`rt_*`) | refused: `E-JIT-RUNTIME-EXTERN-UNBOUND: <name>` |
  | Source, not defined in the module | refused: `E-JIT-UNRESOLVED-CALLEE: <name>` |
  | Unknown origin | refused: `E-JIT-UNKNOWN-CALL-ORIGIN: <name>` |

  A refusal is a `CompileResult.CodegenError` naming module and symbol. Without
  it, the shared lowering would declare the import and the provider would abort
  the host.

Natively linked after: local and Foreign callees. Runtime externs: still 0,
now a named compile error instead of a call through handle 0.

### Follow-up: lowering-owned imports (same lane, continued on Opus)

The named-callee pre-scan did not cover imports the lowering declares by
itself. A JIT `main` holding only the string constant `"hi"` aborted the host:
`PANIC can't resolve symbol rt_string_new_literal`, exit 134 (pinned red by
`jit_lowering_import_fail_closed_spec.spl`, `child-died-by-signal`). Fix:

- Every import declaration in the lowering goes through
  `cl_declare_import_function` (`cranelift_runtime_imports.spl`). That function
  records the name while one JIT module is being compiled.
- `cranelift_jit_run_main` refuses any recorded import that is not a Foreign
  callee of the module: `E-JIT-LOWERING-IMPORT-UNBOUND: <name>`. It does this
  before finalize and frees the module. The check is an allowlist, so a helper
  added to the lowering later is refused too, not aborted on.
- Imported statics are refused up front: `E-JIT-EXTERN-STATIC-UNBOUND: <name>`.
  Their accessor symbol exists only in the providing object.
- A `main` with parameters is refused: `E-JIT-ENTRY`. The entry is called with
  no arguments and read as one i64. The spec pins `-5` and `2^33+1` round-trips.
- Cost: float `%`/`pow` libcalls (`fmod`, `pow`) are now refused in the JIT too,
  because they are not Foreign callees. Before, they would have bound through
  libc.

Seed-signature parity: `cranelift_runtime_import_seed_parity_spec.spl` reads the
seed's `RuntimeFuncSpec` table and the adapter's runtime-import shims as source.
The shims include the lowering-owned `cl_is_lowering_owned_runtime` names. The
spec fails on any new disagreement, and on any recorded one that has
disappeared. There are 10 recorded disagreements:

- Width: `rt_array_push`, `rt_array_set` and `rt_array_set_text` return an i8
  bool in the seed and are read as i64 by the shim.
- Missing from the seed table: 7 names (`rt_raw_f64_to_string`,
  `rt_process_*` (`run_timeout_tuple`, `run_bounded_bytes_tuple`, `run_owned_observed_bounded_text`, `spawn_guarded_value`), `rt_cpuid_tuple_block`,
  `rt_env_get_value`).

None of these is imported by the JIT today, because each one is refused.

## Seed-side fix (lane `work/jit-provider-runtime-symbols-20261113`, Opus)

One table, two builders. `jit::seed_jit_runtime_symbol_table(provider)` is
the runtime symbol table the seed JIT registers: every `RUNTIME_SYMBOL_NAMES`
entry the provider (or the ELF fallback) resolves, plus the compiler-owned
symbols. `JitCompiler::with_provider` and `rt_cranelift_new_module_impl` both
register it through `jit::register_seed_jit_runtime_symbols`. The provider
builds it once, with the seed JIT's `default_runtime_provider()`, and holds the
provider for the process lifetime. There is no second list.

Measured in the seed unit-test build (aarch64): 2008 symbols registered, 1393
of them with a host `RuntimeFuncSpec` row. Those 1393 are the runtime externs
the pure-Simple JIT can link.

Admission happens at declaration (`admit_jit_import`, JIT modules only), so
finalize never meets a symbol it cannot resolve:

| Import | Admitted when |
|---|---|
| runtime-table name, any linkage | its declared signature equals `RuntimeFuncSpec::build_signature(isa default call conv)` exactly |
| runtime-table name with no spec row | never: its ABI cannot be proven |
| other name, linkage 1 (plain import) | the process resolves it (`dlsym`), as cranelift-jit itself does |
| other name, linkage 5 (`CRANELIFT_LINKAGE_RUNTIME_IMPORT`) | never: runtime-table only |

A refused declaration returns 0 and latches the module, as the other provider
refusals do. An AOT module refuses linkage 5. `rt_cranelift_finalize_module`
checks every function and data import against the table and `dlsym` before
`finalize_definitions`, and turns a finalize `Err` into a latched refusal
instead of `unwrap()`. The release profile is `panic = "abort"`, so a
`catch_unwind` would not help; the pre-check is what makes finalize safe.

Pure-Simple side (`cranelift_runtime_imports.spl`, `jit_extern_resolution.spl`,
`cranelift_codegen_adapter.spl`):

- A Runtime callee classifies as `RuntimeImport`, no longer a blanket refusal.
- In a JIT module, `cl_declare_import_function` declares a Foreign callee with
  linkage 1 and every other import (Runtime callees, lowering-owned helpers)
  with linkage 5. A refused name is recorded in the import ledger, and the call
  site emits a placeholder constant so the IR stays well formed.
- `cranelift_jit_run_main` reports each refused name before finalize:
  `E-JIT-RUNTIME-EXTERN-UNBOUND` (Runtime callee), `E-JIT-FOREIGN-EXTERN-UNBOUND`
  (Foreign callee) or `E-JIT-LOWERING-IMPORT-UNBOUND` (lowering-owned).
- The `E-BACKEND-CRANELIFT-CALL-ABI` panics for a Foreign or external callee,
  and the function-value address panic, are returned as errors in a JIT module.
  The AOT lane keeps its panics.

Results:
- `rt_getpid`, `rt_time_now_unix_micros`, `rt_string_new_literal`, `rt_string_len`
  and `rt_file_size` run natively from JIT code. JIT and interpreter return the
  same values (`jit_runtime_extern_interpreter_parity_spec`).
- `rt_file_exists` returns `i8`, and an unknown-signature call reads it as `i64`.
  `rt_array_push` and `rt_array_set` have the recorded shim width mismatches.
  All of these are refused by name, not linked with a wrong width.
- The float libcalls (`fmod`, `pow`) are still refused: they are neither Foreign callees nor runtime-table symbols.
- A Foreign symbol missing from the process is refused by name. Before, it
  aborted the host (exit 134).

## Not covered

- **Exactness stops at Cranelift types.** Admission proves that the declared
  parameter and return types equal the `RuntimeFuncSpec` row. It does not prove
  value representation. A tagged `RuntimeValue` versus a raw integer, or a boxed
  `text` versus a (ptr, len) pair, both travel as `i64`. Agreement there rests on
  the shared MIR lowering's argument conventions. Those are verified only for
  the parity-spec cases. The seed JIT also applies call-site rewrites the
  pure-Simple lowering does not share (`instr/calls.rs`: `boxed_text_arg_indices`,
  text (ptr, len) expansion). A name whose `.spl` declaration disagrees with the
  native return while the types match, such as the seed lane's `rt_pty_*` /
  `rt_file_atomic_write` (`-> bool` against a tagged value), would be admitted.
- Some all-`i64` runtime calls run with whatever arguments MIR passes. For
  example, `rt_process_run` with three zero words reaches `rt_process_run_tuple`
  and runs. The JIT links the symbol; checking the arguments is the caller's job.
- `_cranelift_jit_run` (K1 lane) scans every module and compiles only the
  last. Runtime and Foreign imports of earlier modules are therefore never
  checked against the provider. Cross-module Source calls are refused as
  `E-JIT-UNRESOLVED-CALLEE` rather than linked across JIT modules.
- A module with a public static fails closed with `E-JIT-STATICS`.
  `cranelift_define_global_accessor_v1` always defines through the AOT entry,
  which rejects a JIT handle. The fix is to thread the `jit` flag into
  `declare_module_statics`, or to skip the accessor in a JIT module.
- Other lowering panics (global load/store/address with no declaration, an
  unlowered instruction) still panic in a JIT module.
- `CodegenPipeline.jit()` in `codegen.spl` is unchanged. Its remaining users are
  `jit_compile` / `compile_and_run` and the SMF path.
- A native pure-Simple binary has no JIT at all: `rt_cranelift_*` is a trapping
  stub (`src/runtime/runtime_cranelift_bridge_stub.c`). Everything here was
  verified hosted by the Rust seed (tier T0, aarch64 Linux).
