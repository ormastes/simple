# BUG: `native.spl` native-build lane compiles `runtime.c` (legacy, untagged enum/atomic representation) while the Rust core-c-bootstrap lane compiles `runtime_native.c`/`runtime_legacy_core.c` (modern, tagged-heap representation) — same public symbol names, different internal ABI

**Status:** OPEN — static evidence now points to LATENT (self-consistent, not
currently live), but not empirically proven by a real native build/run (see
"Static evidence" and "Why not fixed here" below)
**Severity:** low-medium as currently evidenced (downgraded from an initial
"high if live" — see "Static evidence"); still worth fixing for consistency/
technical debt, and the risk is NOT zero (see residual gaps)
**Component:** `src/app/compile/native.spl` (`compile_native`, pure-Simple
self-hosted "compile a `.spl` file to a native binary" path, reachable from
the main CLI compile driver via `emit == "native"` /
`backend == "llvm"`, `src/app/io/_CliCompile/compile_opt_and_driver.spl:494`)
vs `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
(`build_c_runtime_library`, the Rust "core-c-bootstrap" lane)
**Found:** 2026-07-20, systematic duplicate-runtime-implementation audit
(see `scripts/check/check-runtime-symbol-lane-divergence.shs`, the sibling
regression check landed alongside this bug)

## Background

This session's mission was to enumerate the "same rt_*/spl_* function
implemented in multiple places, different build lanes pick up different
copies" defect class (3 proven instances landed earlier today: `spl_file_read`
procfs bug in 3 C copies, `rt_array_copy` Rust-only/C-lane-linked-nothing,
`detect_platform` under 11 mangled names).

Enumerating all native-build "lanes" (distinct sets of C files actually
compiled together into one binary) found a THIRD lane not covered by the
prior 3 instances:

- **Lane A** (Rust-seed cdylib): `src/compiler_rust/runtime/build.rs`
  `c_sources` — 11 files, cc::Build.
- **Lane B** (Rust "core-c-bootstrap" native-build):
  `pipeline/native_project/tools.rs` `build_c_runtime_library` —
  `runtime_native.c`, `runtime_legacy_core.c`, `runtime_mcp_core.c`,
  `runtime_fork.c`, `runtime_memtrack.c`, `runtime_process.c`,
  `runtime_font.c`, `runtime_pool.c`, `runtime_simd_utf8.c`,
  `runtime_simd_dispatch.c`, `runtime_framebuffer.c`,
  `runtime_directx_core.c` (+ conditional platform/openssl/sqlite files).
- **Lane C** (pure-Simple self-hosted `compile_native`, `native.spl:390`):
  `-x c src/runtime/runtime.c src/runtime/runtime_thread.c
  src/runtime/runtime_memtrack.c src/runtime/runtime_fork.c`, linked together
  with `find_simple_native_all_library()` (a separate Rust staticlib,
  `native_all` crate, providing "Cranelift SFFI + runtime").

Lane C compiles `runtime.c` — the file whose header literally says `Simple
Bootstrap Runtime Library ... for the bootstrap compiler` and which
`#define`s `SPL_LEGACY_VALUE_RUNTIME 1`. Lane B instead compiles
`runtime_native.c` + `runtime_legacy_core.c`, the modern split-out runtime.
Both files define the SAME ~85 public `rt_*`/`spl_*` symbol names
(`spl_str_*`, `spl_array_*`, `spl_dict_*`, `spl_panic`/`print`/`println`,
`rt_enum_*`, `rt_atomic_*`, `rt_bdd_*`, `rt_signal_*`, `rt_atexit_*`,
`rt_cli_*`, `rt_file_*`, `rt_dir_*`, ...) — see
`scripts/check/runtime_symbol_lane_divergence_baseline.txt` for the full,
nm-verified list (109 symbols total across all lane pairs, most of which are
this runtime.c/runtime_native.c or runtime.c/runtime_legacy_core.c pair).

## Flagship example: `rt_enum_new`

`runtime.c`:
```c
SplRuntimeEnum* value = (SplRuntimeEnum*)SPL_MALLOC(sizeof(SplRuntimeEnum), "enum");
value->enum_id = enum_id;
value->discriminant = discriminant;
value->payload = payload;
return (int64_t)(intptr_t)value;   /* RAW pointer, no tag bit */
```

`runtime_native.c`:
```c
/* interned: identical (enum_id, discriminant, payload) returns the same handle */
RtCoreEnum* value = (RtCoreEnum*)calloc(1, sizeof(RtCoreEnum));
value->kind = RT_VALUE_HEAP_ENUM;
value->enum_id = (uint32_t)enum_id;
value->discriminant = (uint32_t)discriminant;
value->payload = payload;
rt_core_register_enum(value);
int64_t tagged = (int64_t)(((uint64_t)(uintptr_t)value) | RT_VALUE_TAG_HEAP);
/* ... intern table update ... */
return tagged;   /* TAGGED handle (RT_VALUE_TAG_HEAP bit set), GC-registered */
```

Same divergence pattern (short/raw vs long/tagged-and-registered) also hits
`rt_atomic_int_new`/`_load`/`_compare_exchange`, `rt_bdd_*`, `rt_cli_arg_at`,
`rt_file_*` (`SPL_MALLOC`+manual buffer vs different allocator path).

## Static evidence gathered (why this is downgraded to "latent", not "unproven-high")

`runtime.c` is internally self-paired: it ALSO defines `rt_enum_discriminant`,
`rt_enum_id`, `rt_enum_payload` in the same legacy (untagged) representation,
and `RT_VALUE_TAG_HEAP`/`RtCoreEnum`/`rt_core_register_enum` are private to
`runtime_native.c`'s translation unit, not declared in the shared
`runtime.h` both files include. Two follow-up greps (no build required)
narrow the remaining risk:

1. **How does codegen invoke enum ops?** `src/compiler/50.mir/_MirLoweringExpr/
   switch_operators_calls.spl` and `method_calls_literals.spl` lower enum
   construct/discriminant-match/payload-extract to generic MIR **call**
   instructions naming `"rt_enum_new"`/`"rt_enum_discriminant"`/
   `"rt_enum_payload"` (`MirConstValue.Str(...)`) — backend-agnostic call
   emission, not inlined tag-bit arithmetic. Every backend (C included) that
   lowers this MIR just emits a call to the named external symbol. Grepping
   the actual C-backend translate files
   (`70.backend/backend/_CBackendTranslate/*.spl`, `c_backend_translate.spl`,
   `c_ir_builder.spl`) for `rt_enum_*`/`RT_VALUE_TAG_HEAP` finds NOTHING —
   the C backend does not special-case enum handles at all; it only ever
   emits calls to the named accessors. Confirms: no inline tag math outside
   `rt_enum_*` themselves.
2. **Does `native_all` (the Rust staticlib linked alongside `runtime.c` in
   Lane C) do generic tag-bit dispatch on values that could be enum
   handles?** `grep RT_VALUE_TAG_HEAP src/compiler_rust/native_all/src/lib.rs`
   → 0 hits. Broader search for any equivalent tag-mask/heap-tag naming in
   that file → 0 hits. `native_all` has no generic value-tag inspection
   logic at all, so it cannot misinterpret an untagged handle from
   `runtime.c` via that route. Generic array/dict/print operations
   (`spl_array_push`, `spl_print`, etc.) are ALSO among the 109 baselined
   dupes defined directly in `runtime.c` itself (link-order precedence keeps
   a Lane-C binary inside `runtime.c`'s own consistent bubble for these too).

**Conclusion from static evidence:** for a Lane-C binary that stays within
functions `runtime.c`/`runtime_thread.c`/`runtime_memtrack.c`/`runtime_fork.c`
already provide (which is most of the surface, since those files
self-consistently cover construction, accessors, and generic array/dict/print
for the legacy representation), the divergence is currently **latent**, not
live. Residual, still-unverified risk: any Lane-C program that calls a
runtime function ONLY `native_all` provides (not shadowed by one of the 4
Lane-C files) and passes it an enum/atomic/etc. handle created via
`runtime.c` — that combination was not exhaustively enumerated here. This
conclusion is static-analysis-only; it has not been confirmed by actually
building and running a native-compiled program through Lane C.

## Fix direction

Even as latent debt, `runtime_native.c` + `runtime_legacy_core.c` are the
correct, current representation (used by Lane B, the actively-maintained
core-c-bootstrap lane, and consistent with the tagged-heap-value ABI used
elsewhere in the runtime) and `runtime.c` should eventually be retired from
Lane C. The likely root fix is to point `native.spl`'s `rt_sources` at
`runtime_native.c` + `runtime_legacy_core.c` (+ whatever else Lane B needs)
instead of `runtime.c`, NOT to hand-patch `runtime.c`'s individual functions
— but that source-list swap needs its own careful verification pass (symbol
completeness against what `native_all` no longer needs to provide, since Lane
B's file set is bigger than Lane C's current 4 files) rather than being done
speculatively here.

## Regression coverage

`scripts/check/check-runtime-symbol-lane-divergence.shs` (new, this session)
compiles each lane's real C sources with `cc -c` and `nm`s the resulting
objects, so it will catch NEW divergent-symbol pairs the same way this one
was found. All 109 currently-known pairs (including every symbol in this bug)
are baselined in `runtime_symbol_lane_divergence_baseline.txt` so the check
is quiet today; it fails only when a symbol not already in that baseline
starts being defined by two different C files. Run:
`sh scripts/check/check-runtime-symbol-lane-divergence.shs`
