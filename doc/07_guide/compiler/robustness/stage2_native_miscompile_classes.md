# Stage 2 native miscompile classes (Phase 3, 2026-10-25)

Catalog of codegen/lowering defects in the Stage 2 compiler that make Phase 3
objects compile cleanly and then misbehave at run time. Found walking a
hello-world through the Phase 3 `simple` binary (run-27e objects; binaries
`pu3` 49df0a2f .. `p3b6y` 402b63c9). Policy: ship a tagged `@workaround` source
change and a Stage 2 compiled `.o` now; the compiler fix lands separately and
takes effect when Phase 3 rebuilds itself. Status as of 2026-10-25; bug docs are
in `doc/08_tracking/bug/` (some are still on `work/p3fix-*` branches awaiting the
batch landing). Procedure: [Phase 3 manual continuation](../../tooling/bootstrap_failure_collection.md#phase-3-manual-continuation-recipe-measured-2026-10-25).

| # | Class / symptom | Minimal shape | Workaround | Bug doc | Status |
|---|---|---|---|---|---|
| 1 | Struct param copied in promote wrappers: promoted root is a copy, original freed at scope end (dangling, empty panic) | `fn promote<T>(value: T)` wrapper around `rt_transient_heap_promote` | `mut value: T` on both wrappers | `transient_promote_struct_param_copy_dangles` | source fixed, PR #4574 landed |
| 2 | Store to a nonexistent field silently writes field 0 (`CompileOptions.target_opt_ctx` overwrote `mode`; empty panic in `CompileMode.to_text`) | `s.no_such_field = v` | stop using the field; MIR now fails closed on a missing qualified-layout field | `missing_struct_field_store_writes_field0` | source fixed, PR #4587 landed |
| 3 | Match expression whose FIRST arm is `panic(..)` returns const 0 (struct payload: `mov x2,#0; ldr [x2]` SEGV; i64: silently 0). Cause: `lower_bootstrap_panic_call` leaves a unit temp in a fresh block, so the first value arm types the merge local as unit | `val v = match r: case Err(e): panic(e) case Ok(x): x` | put the Ok arm first, or `return` in the error arm (`module_assembly.spl`, 2 sites) | `match_expr_panic_first_arm_drops_result` | workaround object in `fixed_objs`; compiler fix (`switch_operators_calls.spl`) committed, NEEDS-BATCH |
| 4 | `dict[k] ?? d` on `Dict<_, text>` decodes the result via `rt_interp_cstr` before the nil test: a missing key yields raw 0, not `d` (44 sites in `80.driver`; `compiler_source_entry ?? ""` gave "collected zero source files") | `val s = config["k"] ?? ""` | `contains_key` guard | `dict_index_coalesce_text_decoded_before_nil_test` | workaround object appended; compiler fix open |
| 5 | `text?` unwrap goes through `rt_interp_cstr`, an untagged `char*`: truncates at NUL and the data pointer is invisible to transient promotion (B5: string freed at parse scope end, "unresolved name" HIR error) | `val s = opt_text!` with embedded NUL; raw `char*` held in a retained AST | `content ?? ""` in `inventory_scratch.spl` (`@workaround`); runtime classify of untagged words whose `w-16` is a registered transient string | `optional_text_unwrap_truncates_at_nul`, `transient_promote_misses_raw_text_data_pointer` | NUL workaround on release; runtime fix on `work/p3fix-p3b5` 9877fb93efa |
| 6 | Unwrapped `[Struct]?` index loses the element type (element read as scalar) | `val a = f()!; a[i].field` | none recorded; see the bug doc repro | `unwrapped_optional_struct_array_elem_provenance` | open (compiler) |
| 7 | Struct/enum value boxed with `rt_value_int_wide` (`handle<<3`) then read back as a pointer: SEGV. Sites: untyped `val x = if c: <struct> else: <struct ctor>` used as a dict key (B6a); `if val p = opt: arr.push(p)` (B7); 36 `[HirExpr]/[HirBlock]` pushes in `mir_array_move.am_children` (B8); generic `$i64` instance `_sffi_enum_discriminant<i64>(HirExprKind.Call(..))` gives disc -1 (B9); `rt_transient_heap_promote<T>(parsed)` root (B4, 4 sites) | any of the shapes at left | annotate the binding (`val k: SymbolId = if ..`) or `var` + reassign; B4/B7-B9 were binary-patched privately (NOP the box call) | `untyped_val_if_expr_struct_boxed_as_int_dict_key` (B6a); `generic_extern_enum_arg_boxed_as_int` (B4, B7, B8, B9 by site) | B6a workaround object appended; B4 object appended; B7-B9 patched `.o`s (`*_p3b7/p3b8/p3b9.o`) appended to `fixed_objs`; compiler fix open |
| 8 | `[u8] !=` compares references, not elements | `a != b` on `[u8]` | compare element-wise (`_retained_bytes_equal` in `retained_file.spl`, `@workaround`) | `native_u8_array_ne_compares_reference` | workaround on release; compiler fix open |
| 9 | `f(x)?.m()` parsed as an optional chain on the call instead of try-then-member | `f(x)?.m()` | parenthesize: `(f(x)?).m()` (`archive_file.spl` x2) | `indcall_try_then_member` | workaround, PR #4595 landed; 24 latent sites left |
| 10 | Tuple ABI mismatch: C `rt_tuple_new` builds ARRAYS, native code reads tuples as untagged `{e0,e1}` blocks; `rt_env_vars` -> `[(text,text)]?` yields empty names ("environment-field-duplicate") | `for (a, b) in rt_env_vars()` | runtime emits the native layout | `rt_env_vars_tuple_layout_mismatch` | runtime fix on `work/p3fix-p3b10` (0ec0d67e00c, not in `land_queue`); combined B5+B10 runtime object |
| 11 | `Result` tuple / `Optional` payload unsupported in MIR ("unsupported Result tuple payload element type", "payload is Optional, not a tuple"); optional struct stored into a desugared non-optional `has_x/x` field keeps the Option box (B7: `export_attr` strlen SEGV, 349 generated `.?` sites in `hir_codec.spl`) | `Result<(u64, T), E>`, `-> ExportAttr?` stored into `x: T` | rewrite without the tuple/optional payload; construct with nil then `if val p = opt: f.x = p` | `convnodes_retained_file_result_tuple_u64`, `resopt_result_optional_tuple_unwrap` | convnodes workaround PR #4554 landed; resopt workaround still on `work/p3fix-resopt` 7d37644044b (NEEDS-BATCH; #4601 landed only the bug doc and spec); desugared-field case: `optional_struct_stored_into_desugared_field_keeps_option_box` (`work/p3fix-p3b6` 0a45829a649, NEEDS-BATCH); generator fix (`codec_gen.spl` emit `if val p = node.f`) open |
| 12 | Non-public module statics used across modules: Cranelift AOT cannot import them (ICE) | `static` in `vmm.spl` read from `vmm_vma.spl` | declare `pub` | `vmm_static_visibility_cranelift_ice` | fixed in source, PR #4549 landed |
| 13 | MIR go-to-end failures published as PASS: a failed module has no outcome and no object, the shard child sealed it PASS, so 8 modules were dropped silently (run-27e `failed_modules=3`, 7 trap-stubbed at link) | any module with a go-to-end MIR failure | none needed: fail closed | `mir_shard_go_to_end_failure_published_as_pass` (commit d8fc56b23df, `native_mir_shard_module_passed_v1`; ICE row `mir_lower`) | on `work/p3fix-silentmir`, NEEDS-BATCH |

## Diagnosis notes

- A miscompile that reads a constant: grep the disassembly for `mov xN,#0; ldr
  [xN]`. Exactly two sites existed in the whole pu3 binary (class 3).
- A SEGV address of the form `handle<<3` (e.g. `0x5555572449088`) or two packed
  small ints (`0x100000001` = enum_id 1 | disc 1 of an Option box) means class 7 or class 11 (a boxed
  scalar or an Option enum object read as a struct).
- `rt_transient_heap_promote` returns 1 (no-op success, no
  `SIMPLE_TRANSIENT_PROMOTE_DEBUG` line) when the root or a child is untagged and
  not an allocation base, and skips children of packed/bytes arrays. Silence is
  not proof of promotion (runtime_native.c ~3180-3199).
- Prefer a Stage 2 repro (2-minute tiny-entry compile) over reasoning from the
  Phase 3 binary; it decided classes 3, 7 and 10.
