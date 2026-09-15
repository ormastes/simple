# Native-vs-interpreter differential census — 2026-09-13

Harness: `scripts/check/check-native-interp-differential.shs` +
`src/app/test/native_interp_differential.spl` (landed this day).
Wired as one bootstrap-tier `mode=automated` row pinning the `--selftest`
(`config/check/must_check_gates.sdn`); `check-guard-wiring.shs` PASS, 0 NEW unwired.

## Why

Runs 1-24 of the macOS bootstrap chain
(`doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md`) peeled one
native-codegen defect per ~1-hour run, every one of the same shape — the Rust
seed's native pipeline computes a different value than the interpreter for the
same Simple source. Already filed: Optional return-type name loss (#742), LLVM
`.unwrap()` on flat nullables (#746,
`unwrap_family_treats_flat_nil_as_present_2026-09-13.md`), `Poll.unwrap` mangler
rebinds (#750/#757, `unwrap_still_rebinds_to_poll_unwrap_at_closure_scale`),
struct-keyed dict identity after copy (#765,
`dict_struct_key_identity_keyed_copied_key_misses`), `.?` on empty collections
(#771, `native_codegen_dotq_true_on_empty_array`), and `result`-bound text payload
loss (`result_bound_text_payload_lost_in_stage2_native_codegen`).

One defect per bootstrap is not a rate that converges. This census runs the same
spec file on both lanes and diffs per example.

## Configuration

| axis | value |
|---|---|
| seed | `build/cargo-f52/release/simple`, sha256 `7b388bd1f570cb14…`, 2026-09-13 11:08 |
| interpreter lane | `SIMPLE_EXECUTION_MODE=interpreter <seed> run <spec>` |
| native lane | `SIMPLE_NATIVE_BUILD_RUST=1 <seed> native-build --mode dynload --backend cranelift --entry-closure --threads 1` |
| host | `aarch64-apple-darwin`, loaded |
| per-spec caps | build 600 s, native run 120 s |

`build-gpu-seed.shs --verify` on **both** seeds is honestly RED and is recorded
rather than hidden: `cargo-f52` FAILs 2 probe specs
(`metal_msl_pipeline_spec`, `wffi_into_bytes_spec`), `cargo-r2` FAILs 1
(`wffi_into_bytes_spec`). `f52` was used as the newest. Neither seed carries the
`llvm` cargo feature — `--backend llvm` is refused outright — so **the
LLVM-lowering half of the chain's family (#746) is out of this harness's reach**
until an llvm-featured seed exists. The cranelift lane is what was measured.

## The non-vacuity control (read this before trusting any row)

`scripts/check/check_engine_differential.spl`'s header states that
`describe`/`it`/`expect` are Rust interpreter intrinsics **with no codegen
lowering at all**, and concludes that every spec-visible defect in the JIT or
native lane is "invisible to `bin/simple test`, permanently". If that were still
true of this seed, every spec would report all-pass natively and this census
would be a greenwash reporting `0 divergent`.

It is stale for the 2026-09-13 seed. Control: a copy of a green spec, edited so
two of its four `expect(...)` assertions assert a deliberately wrong value,
native-built with exactly the configuration above, prints

```
  camel-cases space-separated words without leaking numeric char codes fail
  camel-cases underscore-separated words too fail
4 examples, 2 failures
```

— the two edited examples, by name, and only those. The native lane discriminates.
(The control spec was not committed: a permanently-red spec in the tree is debt,
and the evidence is the transcript above.)

## Method notes worth keeping

- **`sort | head -N` is not a sample.** The first curation took the
  alphabetically first 60 filtered paths, which on this tree is 60 consecutive
  `test/01_unit/compiler/50.mir/hwir_*` specs — one directory, one feature. The
  harness now stride-samples each root and interleaves.
- **The oracle is the interpreter**, so a spec red on BOTH lanes is an ordinary
  product bug, not a divergence, and is dropped.
- **A spec that fails to native-build is a divergence** of class `build-failed` /
  `link`, never a skip.
- **A spec whose interpreter run produced zero examples is `no-oracle`** and is
  excluded from `compared` — counting it would let "both lanes said nothing" read
  as agreement.
- The spec harness transitively declares five process/mmap externs
  (`rt_exec`, `rt_execute_native`, `rt_get_host_target_code`, `rt_mmap`,
  `rt_process_run_with_limits`) that live in the Rust runtime crate and can never
  be defined by the C-only CoreCBootstrap lane. Builds are attempted **closed**
  first and only retried with `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` when the
  unresolved set is a subset of that inert allowlist, with the retry recorded per
  row. A bypassed binary carries a NULL GOT slot per name, so a `crash` row must
  be triaged to a faulting pc before it is called codegen: pc `0x0` is a
  runtime-lane gap, not bad generated code.

## Results — 48 specs compared (12 no-oracle, excluded), **36 divergent rows**

Curated set: 60 stride-sampled pure-logic specs from `test/01_unit/lib/common` and
`test/01_unit/compiler`, all 60 run. 12 produced no interpreter examples and are
excluded as `no-oracle` rather than counted as agreement.

| class | rows | specs | smallest reproducer |
|---|---|---|---|
| `other` | 14 | `ui/render_opt/occlusion_spec.spl` (8), `crypto/hmac_sha1_spec.spl` (5) | `crypto/hmac_sha1_spec.spl` — all RFC-2202 test vectors pass interpreted, fail natively |
| `link` | 9 | `encoding/{utf32_byte_guard,protobuf_wire_bounds_guard,codec_decode_byte_guard}`, `search/explain_contract`, `engine/math3d_trig_precision_repro`, `web/{browser_renderer_frame_reuse_protocol,browser_session_html_text_level_tags}`, `compiler/{backend/llvm_ir_builder,ast_arena_generation}` | `encoding/utf32_byte_guard_spec.spl` — unresolved `rt_utf8_validate` / `rt_utf8_find_invalid` / `rt_utf8_count_codepoints` |
| `int-width-bitops` **(MISNAMED — see below)** | 5 | `bytes/ints_spec.spl` | `U32le.of(0xDEADBEEF).to_span()` then `U32le.load(sp,0).value()` — `ints_spec.spl:38-42`. **Root-caused 2026-09-13: not an integer-width defect at all.** The six `ints.spl` structs' same-named instance methods (`store`/`to_span`) collapse to a single implementation (`U32be`'s) under native codegen; bit ops are correct at every width. See `doc/08_tracking/bug/native_cross_module_same_name_methods_collapse_to_one_impl_2026-09-13.md`. Reclassify as `method-dispatch`. |
| `crash` | 5 | `text_advanced_return_types_spec.spl`, `wine_process_session_{import_resolution,first_import_module,loader_state}_spec.spl`, `compiler/50.mir/hwir_aspect_lock_spec.spl` | `text_advanced_return_types_spec.spl` — SEGV at `StringBuilder_dot_to_text+16`, `ldr x28,[x8]`, x8 null |
| `truncated-run` | 1 | `token_budget_spec.spl` | native run prints one example name then exits rc=65 with no summary line |
| `build-failed` | 2 | `imaging/find_diff_regions_spec.spl` (+1) | — |

Only 1 of 48 compared specs came from `test/01_unit/compiler` with a divergence in
`other`; the compiler tree's contribution is concentrated in `link` and `crash`.

The three `wine_process_session_*` crashes share a module and are almost certainly
one defect seen three times, not three.

The first `crash` row was triaged to a faulting pc before being called codegen: all
three fault **inside generated code**, not at pc `0x0`, so none is an artifact of
the allowlisted unresolved-runtime bypass.

## Filed this run (new classes only)

- `doc/08_tracking/bug/core_c_bootstrap_runtime_lane_missing_rt_utf8_math_array_symbols_2026-09-13.md` — the `link` class. Six Rust-runtime-only symbols (`rt_utf8_validate`, `rt_utf8_find_invalid`, `rt_utf8_count_codepoints`, `rt_math_sqrt`, `rt_numeric_dot_f64`, `rt_array_remove`) that the C-only CoreCBootstrap lane can never define, with an observed consequence.
- `doc/08_tracking/bug/native_stringbuilder_to_text_segv_null_receiver_2026-09-13.md` — the `crash` class, with the faulting instruction.
- `doc/08_tracking/bug/native_u32_u64_span_roundtrip_loses_value_2026-09-13.md` — the `int-width-bitops` class. **Root cause superseded** by `doc/08_tracking/bug/native_cross_module_same_name_methods_collapse_to_one_impl_2026-09-13.md` (same-named instance methods on sibling types collapse to one implementation natively; the class label `int-width-bitops` is wrong).

Known classes are cited, not duplicated: #742, #746, #750/#757, #765, #771 and
`result_bound_text_payload_lost_in_stage2_native_codegen_2026-09-13.md`.
`other` (occlusion, hmac_sha1) is left unfiled deliberately — the class is a
grouping hint, and neither has been reduced to a minimal shape yet.

## One parser trap worth keeping

A spec's own `print` output interleaves on the native runner's example line
(`  test full line 1tokens: [t, t]`), so name-keyed matching alone reported
`_cmm_debug_spec.spl` as two divergences when both lanes said `2 examples, 0
failures`. The driver now takes the **summary pair as the primary oracle** and
uses per-example names only to say *which* example, never *that* there was a
divergence.
