# Pure-Simple JIT cannot link `rt_*` externs: the Cranelift provider registers no runtime symbols

- **Filed:** 2026-11-13
- **Status:** OPEN. Blocked on a seed-side change outside `src/compiler/**`.
- **Related:** `jit_caret_392_unregistered_externs_hybrid_splice_2026-11-13.md` (the seed JIT's own 392-extern splice; a different code path with the same root shape)
- **Pinned by:** `test/01_unit/compiler/backend/jit_runtime_extern_native_link_spec.spl` (`@tag:in-development`, 0/2 today)

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
disappeared. There are 12 recorded disagreements:

- Width: `rt_array_push`, `rt_array_set` and `rt_array_set_text` return an i8
  bool in the seed and are read as i64 by the shim.
- Missing from the seed table: 9 names (`rt_raw_f64_to_string`,
  `rt_process_*_tuple`/`_value`/`_text`, `rt_cpuid_tuple_block`,
  `rt_env_get_value`).

None of these is imported by the JIT today, because each one is refused.

## Fix needed (seed side, not done here)

Register the runtime symbol table on the `JITBuilder` in
`rt_cranelift_new_module_impl`, the same table the seed's own JIT uses
(`src/compiler_rust/common/src/runtime_symbols.rs`). Then, on the pure-Simple
side:

1. Lift the `RuntimeUnbound` refusal in `jit_classify_callee` for the names the
   provider registers. The provider must expose that set or a lookup; a second
   hand-kept name list in `.spl` is not acceptable.
2. Check the import ABI before lifting it. The shared lowering derives a Runtime
   import's signature from the `.spl` `extern fn` declaration. The seed's native
   symbols follow `RuntimeFuncSpec` (`runtime_sffi.rs`), where a `text` argument
   is a (ptr, len) pair and some returns are tagged values. The seed lane's own
   exclusion list (`rt_pty_*`, `rt_file_atomic_write`: declared `-> bool`, native
   returns a tagged value or `i64`) shows the two disagree for real names.
3. Remove the tag from `jit_runtime_extern_native_link_spec.spl`.

## Not covered

- `_cranelift_jit_run` (K1 lane) scans every module and compiles only the
  last. Cross-module Source calls are refused as `E-JIT-UNRESOLVED-CALLEE`
  rather than linked across JIT modules.
- A module with a public static fails closed with `E-JIT-STATICS`.
  `cranelift_define_global_accessor_v1` always defines through the AOT entry,
  which rejects a JIT handle. The fix is to thread the `jit` flag into
  `declare_module_statics`, or to skip the accessor in a JIT module.
- Some failures still panic instead of returning an error. A Foreign callee
  with an ABI mismatch reaches `panic` in the lowering, and so does a function
  value with no address. A Foreign symbol that is missing from the process
  still aborts at the provider's `finalize_definitions().unwrap()`. The
  pre-finalize allowlist only proves an import is Foreign, not that the process
  can resolve it.
- Passing the runtime-import parity check does not prove the ABI of a Runtime
  callee whose signature comes from its `extern fn` declaration. That import
  is refused today, so the gap is latent until the provider registers symbols.
- `CodegenPipeline.jit()` in `codegen.spl` is unchanged. Its remaining users are
  `jit_compile` / `compile_and_run` and the SMF path; the defects listed
  above are still there.
- A native pure-Simple binary has no JIT at all: `rt_cranelift_*` is a trapping
  stub (`src/runtime/runtime_cranelift_bridge_stub.c`). Everything here was
  verified hosted by the Rust seed (tier T0).
