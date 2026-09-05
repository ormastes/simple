# CENSUS: declared-return-type mismatches (WARN phase)

- **Date:** 2026-08-10
- **Stream:** N2 (relaunch of K1)
- **Bug:** `doc/08_tracking/bug/declared_return_type_not_enforced_2026-08-09.md`
- **Companion:** `doc/08_tracking/bug/dotq_tail_position_in_bool_returning_fns_2026-08-09.md`
- **Status:** step 2 of the agreed `warn -> census -> error` sequence. **NOT promoted
  to error** — that is an owner decision and the numbers below are its input.

## What produced these numbers

- Checker: `src/compiler/35.semantics/lint/return_type_mismatch.spl` (WARNING
  severity only; fails no build, is not wired into any gate).
- Runner: `scripts/check/census-return-type-mismatch.spl`
- Binary: `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime
  Aug 9 23:10). The Rust seed. No behavioural claim below depends on the engine —
  the census is a static text scan; the only *executed* claims are in the bug doc.
- Command: `simple run scripts/check/census-return-type-mismatch.spl --list src test scripts`
- Scan roots are named explicitly (`src test scripts`). A recursive walk from the
  repo root drags in `build/` and `target/` and dies without output.

**Self-control, run before every scan and required to pass:** 5 planted
violations (one per code) must be detected and 13 deliberately-correct forms must
stay silent. Verdict `control: 5 planted violations detected, 13 correct forms
silent`. Without this the scan is not attempted and the script reports
`ERROR -- positive control did not reproduce`.

## Headline

```
files scanned                 : 35273
findings (raw, incl. dup tree): 122
findings (deduped)            : 110
```

`test/01_unit` and `test/unit` both execute and hold the same specs; **deduped**
collapses that mirror, **raw** does not. Both are reported throughout, per the
standing rule.

## By class (deduped / raw)

| Code | Class | Deduped | Raw |
|------|-------|---------|-----|
| RET001 | tail-expression mismatch | 14 | 17 |
| RET002 | `.?` in a value position of a non-Option fn | 28 | 29 |
| RET003 | `return <expr>` type mismatch | 0 | 0 |
| RET004 | tail statement yields no value | 18 | 20 |
| RET005 | `pass` stub under a `-> T` signature | 50 | 56 |
| | **total** | **110** | **122** |

RET003 being zero is a real result, not a hole: the control plants a RET003 and
detects it. Explicit `return <literal>` of the wrong type essentially does not
occur; the defect lives in *implicit tail position*, which is exactly the rule
nobody was checking.

## By declaration kind (deduped / raw)

| Kind | Deduped | Raw |
|------|---------|-----|
| free_fn | 73 | 84 |
| impl_method | 14 | 14 |
| trait_method | 10 | 10 |
| nested_fn | 7 | 7 |
| class_method | 6 | 7 |

**Generics: 0.** No finding carried the `+generic` suffix. The bug doc named
generics as a reason the real checker is hard; for the *corpus repair* they are
not a blocker.

Lambdas: 0 — but this is a **scan limitation, not a measurement**. The checker
recognises `fn`/`me` declaration headers only, so `->` on a lambda is never
examined. Lambdas remain uncensused.

## By declared return type (deduped / raw)

`-> bool` 35/36 · `-> i64` 25/31 · `-> text` 16/17 · `-> [i64]` 6/6 ·
`-> u64` 6/6 · `-> [u8]` 3/5 · `-> [text]` 3/3 · `-> usize` 3/3 · `-> u16` 3/3 ·
`-> f64` 2/2 · `-> u8` 2/2 · `-> u32` 2/2 · `-> i32` 2/3 · `-> [BlockId]` 1/1 ·
`-> [NarrowingFact]` 1/2

`-> bool` is the single largest bucket, which is the signature of the `.?`
family.

## Cross-check against the companion bug

The `.?` bug found 42 sites in `-> bool` functions; 16 were genuinely wrong and
are FIXED in `48537735be4`. This census, run after that fix, reports 28 deduped
RET002. Those two numbers are consistent: 42 − 16 ≈ 26, and RET002 also catches
`.?` tails under non-`bool` declared types that the companion sweep did not
enumerate. Per instruction, **no `.?` site was touched by this stream** — they
are counted and left.

## How much to trust the number

**110 is a floor, never a ceiling.** The checker is fail-quiet by construction:

- An expression is classified only when the classification is beyond doubt —
  literals, comparisons, `not`, `.?`. Anything containing a call, a variable, a
  field access, a generic, or an `if`/`match` classifies UNKNOWN and is never
  reported.
- The declared side is scored only for bool/int/float/text/array. `Option`,
  `Result`, every user type and every generic accept anything.
- `and`/`or` are deliberately not read as bool evidence — they are also the
  bitwise integer operators.
- Lambdas are not examined at all (above).

So the true violation count is higher than 110, and by an unknown factor. That
bias is the correct one for a number feeding a promote-to-error decision: it
cannot overstate the case for promotion.

Known suppressions that were *added* after over-reporting in earlier runs, each
of which would otherwise inflate the count:

| Guard | Would have added |
|-------|------------------|
| `decl != ""` gate on RET004 (void/Option/user types) | 224 phantom findings |
| `return if c: a else: b` reads the ARMS not the condition | 42 phantom RET003 |
| triple-quoted regions masked before the line walk | 10 of 11 RET004 |
| `loop` matched as a whole keyword, not a prefix | 2 (`loopback`, `loop_ref`) |

## CORRECTION 2026-08-10 (stream P3): RET001 and RET004 are 100% FALSE POSITIVES

The repair pass below was commissioned against "60 deduped real type
violations" (RET001 14 + RET002 28 + RET004 18). **32 of those 60 are not
violations at all.** Every RET001 and every RET004 finding was re-checked
against the real function body, located by NAME rather than by the reported
line, and all 32 are correct code. The corpus-repair bill in item 2 below is
wrong and must not be used to size the promotion work.

### Why the census misreports

The reported line is the declaration line **+1**, i.e. it points at the
docstring, and the classifier reads its `actual=` from the wrong region:

- **`actual=text` (8 of 14 RET001)** is the function's `"""docstring"""` being
  read as the tail expression. The doc's own note that triple-quoted regions
  are "masked before the line walk" holds for RET004 but **not** for the
  RET001 tail classifier.
- **`actual=bool` is the PRECEDING function's tail.** `_pow2_i64`
  (`formula.spl`) is reported `actual=bool`; its real tail is `result` (i64).
  The `bool` comes from `_is_nonneg_int` immediately above it, whose tail is
  `v >= 0.0 and v == v.to_i64().to_f64()`.
- **RET004 `<no value>` is a multi-line or call tail.** `emit_vssrl_vv`'s tail
  is `_encode_rvv_fp(...)` — a call, which the doc states classifies UNKNOWN
  and should never be reported. `breakpoint_probe_serial_evidence_contract_line`
  ends in a `+`-continued string concatenation spanning 14 lines; the line
  walk cannot see a tail expression that is not on one line, so it concludes
  the tail yields nothing.

Representative verified-correct sites (real tails in parentheses):
`_pow2_i64` (`result`), `_pow2` (`result`), `extract_feature_ids` (`ids`),
`make_two_stored_blocks` (`data`), `_aes_gcm_make_j0` (`j0`),
`proc_slot_active` (`0` / `rt_atomic_int_load(...)`), `is_numeric_type` and
`get_successor_blocks` (match arms), `recall` and `cosh_approx` (arithmetic),
`cose_tag_mac0` (`17`), `cose_alg_eddsa` (`return -8`).

The three `total_allocated -> usize` findings are trait-method declarations
with a docstring and no body — that is RET005 (stub), not RET001.

**Consequence:** the counts are not merely a floor (as the doc states), they
are also inflated by false positives in two of the four codes. Fix the
classifier before this census is used to gate anything.

### RET002 re-verification

The 28 remaining RET002 sites are the accidentally-correct residue left by
`48537735be4`, which had already fixed the 16 genuinely-wrong ones. Re-checked
by payload type: the struct/tuple-payload sites (`MirFunction?`,
`PeCodeViewInfo?`, `(text, PossibleInstantiation)?`, symbol/table/db handles)
are safe, and rewriting them would be churn. **One genuinely-wrong class was
found and fixed:** `LazySeq.any` in `src/app/interpreter/lazy/lazy_seq.spl:415`
and `lazy_seq_fixed.spl:413`, which was `self.find(predicate).?` over
`find(...) -> T?` with a *generic* payload. Measured on both engines:

```
                 interpreter      jit
any_old(has 0)   0   (raw i64!)   false   <- WRONG, element 0 does match
any_old(no 0)    nil              false
any_new(has 0)   true             true
any_new(no 0)    false            false
```

`.?` in tail position of `-> bool` leaks the raw payload out of the function on
the interpreter and is *unconditionally false* for a falsy payload on the JIT,
so `any` answered false for any element equal to `0` / `""` / `false`. Rewritten
as `self.find(predicate) != nil`, which is correct and engine-agreeing.

The `text?`-payload sites (`has_subcommand`, `has_js_glue`,
`optimization_rule_provider_missing_fact`) are the same hazard class in
principle but carry values that are never empty in practice; left alone and
recorded here rather than churned.

## Recommendation (for the owner, not acted on here)

1. RET005 (50) is the largest bucket but is a **different defect** — declaration
   stubs under value-returning signatures, not logic that computed the wrong
   type. Triage it separately; it should not gate promotion.
2. RET001 + RET002 + RET004 = **60 deduped** real type violations. That is the
   corpus-repair bill for promoting to error.
3. Before promotion, census lambdas — the one class this scan cannot see.
4. Engine divergence on tail-position semantics (bug doc fact 3) must still be
   resolved first; enforcing a contract the backends implement differently only
   relocates the bug.

## Full finding list

Format: `CODE file:line fn declared=-> T actual=A kind=K`. Raw list (122 rows,
including the `test/01_unit` ≡ `test/unit` mirror).

See `scripts/check/census-return-type-mismatch.spl --list src test scripts` to
regenerate. The complete enumeration follows.

```
RET002 src/compiler/70.backend/linker/macho_inspect.spl:204 macho_has_uuid declared=-> bool actual=option kind=free_fn
RET002 src/compiler/70.backend/linker/pe_parser.spl:299 pe_has_codeview declared=-> bool actual=option kind=free_fn
RET005 src/compiler/70.backend/backend/common/type_mapper.spl:33 map_primitive declared=-> text actual=<stub> kind=trait_method
RET005 src/compiler/70.backend/backend/common/type_mapper.spl:40 map_pointer declared=-> text actual=<stub> kind=trait_method
RET001 src/compiler/70.backend/backend/native/_ArmNeon/encoding_primitives.spl:649 encode_neon_f32x4_3reg declared=-> [i64] actual=text kind=free_fn
RET004 src/compiler/70.backend/backend/native/encode_rvv_fixedpt.spl:83 emit_vssrl_vv declared=-> [i64] actual=<no value> kind=free_fn
RET004 src/compiler/70.backend/backend/native/encode_rvv_fixedpt.spl:133 emit_vsadd_vv declared=-> [i64] actual=<no value> kind=free_fn
RET004 src/compiler/70.backend/backend/native/encode_rvv_mask.spl:100 emit_vmor_mm declared=-> [i64] actual=<no value> kind=free_fn
RET004 src/compiler/70.backend/backend/native/encode_rvv_mask.spl:112 emit_vmor_not_mm declared=-> [i64] actual=<no value> kind=free_fn
RET002 src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:291 hardware_call_uses_port_map declared=-> bool actual=option kind=impl_method
RET002 src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:854 call_is_lowered_hardware_entity declared=-> bool actual=option kind=impl_method
RET002 src/compiler/70.backend/backend/llvm_backend.spl:344 has_object_code declared=-> bool actual=option kind=impl_method
RET002 src/compiler/70.backend/backend/wasm_backend.spl:693 has_js_glue declared=-> bool actual=option kind=impl_method
RET001 src/compiler/70.backend/codegen_enhanced.spl:379 is_numeric_type declared=-> bool actual=text kind=nested_fn
RET002 src/compiler/35.semantics/const_keys.spl:297 can_validate declared=-> bool actual=option kind=impl_method
RET002 src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl:276 optimization_rule_provider_can_run declared=-> bool actual=option kind=free_fn
RET001 src/compiler/60.mir_opt/mir_opt/dce.spl:272 get_successor_blocks declared=-> [BlockId] actual=text kind=impl_method
RET005 src/compiler/60.mir_opt/mir_opt/mod.spl:55 mir_opt_is_inline_pass declared=-> bool actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:20 im_hashmap_new declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:32 im_hashmap_insert declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:43 im_hashmap_get declared=-> text actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:54 im_hashmap_remove declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:65 im_hashmap_contains_key declared=-> bool actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:75 im_hashmap_len declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:85 im_hashmap_keys declared=-> [text] actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:95 im_hashmap_values declared=-> [text] actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:114 im_vector_new declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:125 im_vector_push_back declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:136 im_vector_push_front declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:147 im_vector_get declared=-> text actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:159 im_vector_set declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:169 im_vector_len declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:208 im_hashset_new declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:219 im_hashset_insert declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:230 im_hashset_remove declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:241 im_hashset_contains declared=-> bool actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:251 im_hashset_len declared=-> i64 actual=<stub> kind=free_fn
RET005 src/compiler/90.tools/ffi_gen/specs/im_rs.spl:261 im_hashset_to_array declared=-> [text] actual=<stub> kind=free_fn
RET005 src/compiler/95.interp/execution/mod.spl:24 compile declared=-> text actual=<stub> kind=trait_method
RET005 src/compiler/95.interp/execution/mod.spl:26 execute declared=-> text actual=<stub> kind=trait_method
RET005 src/compiler/95.interp/execution/mod.spl:28 has_function declared=-> bool actual=<stub> kind=trait_method
RET005 src/compiler/95.interp/execution/mod.spl:30 backend_name declared=-> text actual=<stub> kind=trait_method
RET002 src/compiler/99.loader/jit_instantiator.spl:200 can_jit_instantiate declared=-> bool actual=option kind=class_method
RET002 src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:957 try_register_bootstrap_global_symbol declared=-> bool actual=option kind=impl_method
RET002 src/compiler/25.traits/associated_types.spl:42 is_resolved declared=-> bool actual=option kind=impl_method
RET002 src/compiler/25.traits/trait_def.spl:58 has_default declared=-> bool actual=option kind=impl_method
RET001 src/app/test/scaffold.spl:247 extract_feature_ids declared=-> [i64] actual=text kind=free_fn
RET002 src/app/interpreter/lazy/lazy_seq.spl:415 any declared=-> bool actual=option kind=nested_fn
RET002 src/app/interpreter/lazy/lazy_seq_fixed.spl:413 any declared=-> bool actual=option kind=nested_fn
RET001 src/app/io/process_governor.spl:94 proc_slot_active declared=-> i64 actual=text kind=free_fn
RET001 src/app/office/sheets/formula.spl:9074 _pow2_i64 declared=-> i64 actual=bool kind=free_fn
RET002 src/app/pkg/lock.spl:47 has_entry declared=-> bool actual=option kind=impl_method
RET002 src/app/pkg/manifest.spl:108 has_dep declared=-> bool actual=option kind=impl_method
RET002 src/lib/nogc_sync_mut/database/server/durability.spl:353 durable_file_loads declared=-> bool actual=option kind=free_fn
RET002 src/lib/nogc_sync_mut/database/bug.spl:150 is_split_table_db declared=-> bool actual=option kind=class_method
RET005 src/lib/nogc_sync_mut/engine/render/graph_ir3d.spl:83 begin_pass declared=-> i64 actual=<stub> kind=class_method
RET002 src/lib/nogc_sync_mut/cli/simple_parser_api.spl:64 has_subcommand declared=-> bool actual=option kind=impl_method
RET002 src/lib/nogc_sync_mut/ffi/llvm_loader.spl:41 llvm_load declared=-> bool actual=option kind=free_fn
RET001 src/lib/nogc_sync_mut/io/process_governor.spl:135 proc_slot_active declared=-> i64 actual=text kind=free_fn
RET002 src/lib/nogc_sync_mut/sffi/llvm_loader.spl:41 llvm_load declared=-> bool actual=option kind=free_fn
RET001 src/lib/nogc_sync_mut/allocator.spl:83 total_allocated declared=-> usize actual=text kind=trait_method
RET004 src/lib/common/science_math/ml_metrics.spl:173 recall declared=-> f64 actual=<no value> kind=nested_fn
RET004 src/lib/common/complex/utilities.spl:311 cosh_approx declared=-> f64 actual=<no value> kind=free_fn
RET004 src/lib/common/crypto/aes_gcm.spl:759 _aes_gcm_make_j0 declared=-> [u8] actual=<no value> kind=free_fn
RET002 src/lib/gc_async_mut/cli/simple_parser_api.spl:61 has_subcommand declared=-> bool actual=option kind=impl_method
RET001 src/lib/gc_async_mut/allocator.spl:83 total_allocated declared=-> usize actual=text kind=trait_method
RET002 src/lib/nogc_async_mut/cli/simple_parser_api.spl:61 has_subcommand declared=-> bool actual=option kind=impl_method
RET002 src/lib/nogc_async_mut/database/bug.spl:150 is_split_table_db declared=-> bool actual=option kind=class_method
RET001 src/lib/nogc_async_mut/allocator.spl:83 total_allocated declared=-> usize actual=text kind=trait_method
RET005 src/compiler_rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl:83 _rt_execute_command declared=-> text actual=<stub> kind=nested_fn
RET005 src/compiler_rust/lib/std/src/tooling/todo_parser.spl:414 _rt_file_read_text declared=-> text actual=<stub> kind=nested_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:8 read_u8 declared=-> u8 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:12 read_u16 declared=-> u16 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:16 read_u32 declared=-> u32 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:20 read_u64 declared=-> u64 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:41 volatile_read_u8 declared=-> u8 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:45 volatile_read_u16 declared=-> u16 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:49 volatile_read_u32 declared=-> u32 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/mem.spl:79 compare declared=-> i32 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/startup.spl:56 interrupts_enabled declared=-> bool actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/time.spl:8 cycles declared=-> u64 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/time.spl:12 micros declared=-> u64 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/time.spl:16 millis declared=-> u64 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/time.spl:33 ticks declared=-> u64 actual=<stub> kind=free_fn
RET005 src/compiler_rust/lib/std/src/bare/time.spl:38 ticks_per_second declared=-> u64 actual=<stub> kind=free_fn
RET002 src/compiler_rust/lib/std/src/core/regex_api.spl:458 is_match declared=-> bool actual=option kind=free_fn
RET002 src/compiler_rust/lib/std/src/verification/lean/runner.spl:102 is_environment_error declared=-> bool actual=option kind=class_method
RET005 src/compiler_rust/lib/std/src/context_manager.spl:37 __exit__ declared=-> bool actual=<stub> kind=trait_method
RET004 src/os/services/netstack/icmpv6.spl:276 icmpv6_compute_checksum declared=-> u16 actual=<no value> kind=free_fn
RET002 src/os/services/vfs/vfs.spl:142 in_container declared=-> bool actual=option kind=nested_fn
RET004 src/os/baremetal/profile/breakpoint_counter.spl:436 breakpoint_sampled_only_fallback_state declared=-> text actual=<no value> kind=free_fn
RET004 src/os/baremetal/profile/breakpoint_counter.spl:635 breakpoint_restore_original_opcode_encoding declared=-> text actual=<no value> kind=free_fn
RET004 src/os/baremetal/profile/breakpoint_counter_probe_image.spl:61 breakpoint_probe_image_source_path declared=-> text actual=<no value> kind=free_fn
RET004 src/os/baremetal/profile/breakpoint_counter_probe_image.spl:64 breakpoint_probe_image_generated_linker_script_path declared=-> text actual=<no value> kind=free_fn
RET004 src/os/baremetal/profile/breakpoint_counter_probe_image.spl:173 breakpoint_probe_serial_evidence_contract_line declared=-> text actual=<no value> kind=free_fn
RET004 src/os/baremetal/profile/breakpoint_counter_probe_image.spl:193 breakpoint_probe_serial_evidence_runtime_line declared=-> text actual=<no value> kind=free_fn
RET001 src/os/crypto/bcrypt.spl:406 _pow2 declared=-> i64 actual=text kind=free_fn
RET004 src/os/crypto/cose.spl:47 cose_alg_eddsa declared=-> i64 actual=<no value> kind=free_fn
RET004 src/os/crypto/cose.spl:60 cose_tag_mac0 declared=-> i64 actual=<no value> kind=free_fn
RET004 test/fixtures/structural/profile_golden_v1.spl:69 profile_golden_resolve_smf_hex declared=-> text actual=<no value> kind=free_fn
RET001 test/01_unit/compiler/semantics/narrowing_spec.spl:69 analyze_nil_check declared=-> [NarrowingFact] actual=bool kind=free_fn  [dup-tree]
RET004 test/01_unit/app/office/sheets/formula_subtotal_fin_spec.spl:58 _eval_kform declared=-> text actual=<no value> kind=free_fn  [dup-tree]
RET001 test/01_unit/lib/common/deflate_inflate_spec.spl:218 make_two_stored_blocks declared=-> [u8] actual=text kind=free_fn  [dup-tree]
RET004 test/01_unit/lib/nogc_async_mut/http/h2/hpack_huffman_spec.spl:54 make_indexed declared=-> [u8] actual=<no value> kind=free_fn  [dup-tree]
RET002 test/01_unit/spec/package_unfold_spec.spl:119 is_unfolded declared=-> bool actual=option kind=class_method  [dup-tree]
RET001 test/01_unit/os/shell/awk_spec.spl:332 _run_awk_exit declared=-> i32 actual=text kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:32 probe_parse_only declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:40 probe_register_only declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:48 probe_direct_load declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:58 probe_wildcard_filter declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:64 probe_lazy_struct declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/03_system/interpreter/lazy_shb_probe.spl:68 probe_unused_broken declared=-> i64 actual=<stub> kind=free_fn  [dup-tree]
RET005 test/system/interpreter/lazy_shb_probe.spl:33 probe_parse_only declared=-> i64 actual=<stub> kind=free_fn
RET005 test/system/interpreter/lazy_shb_probe.spl:41 probe_register_only declared=-> i64 actual=<stub> kind=free_fn
RET005 test/system/interpreter/lazy_shb_probe.spl:49 probe_direct_load declared=-> i64 actual=<stub> kind=free_fn
RET005 test/system/interpreter/lazy_shb_probe.spl:59 probe_wildcard_filter declared=-> i64 actual=<stub> kind=free_fn
RET005 test/system/interpreter/lazy_shb_probe.spl:65 probe_lazy_struct declared=-> i64 actual=<stub> kind=free_fn
RET001 test/unit/compiler/semantics/narrowing_spec.spl:69 analyze_nil_check declared=-> [NarrowingFact] actual=bool kind=free_fn
RET001 test/unit/lib/common/deflate_inflate_spec.spl:218 make_two_stored_blocks declared=-> [u8] actual=text kind=free_fn
RET004 test/unit/lib/nogc_async_mut/http/h2/hpack_huffman_spec.spl:54 make_indexed declared=-> [u8] actual=<no value> kind=free_fn
RET001 test/unit/os/shell/awk_spec.spl:332 _run_awk_exit declared=-> i32 actual=text kind=free_fn
RET002 test/unit/spec/package_unfold_spec.spl:119 is_unfolded declared=-> bool actual=option kind=class_method
```
