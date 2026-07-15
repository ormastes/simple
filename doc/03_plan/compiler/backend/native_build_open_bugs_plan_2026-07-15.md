# Native-build Open Bugs — Remediation Plan (2026-07-15)

Companion to `native_entry_build_correctness_2026-07-14.md`. Enumerates every
**open** `native-build --entry` bug in `doc/08_tracking/bug/native_*`, with root
cause, fix approach, fix site, effort, and an ordered execution plan. Resolved
bugs (array-concat, dict-from-call keys, Result.unwrap→161, top-level `.len()`,
cross-fn text-payload race, static-ctor nil-crash) are excluded — see the
companion doc.

## Verification contract (per fix, unchanged)

- **Oracle:** `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`.
- **Native:** `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
- Native output must equal the oracle, **or** be correct-by-construction where the
  oracle is provably broken. A loud build failure is **never** silently converted
  to a wrong answer.
- Gates: `native-smoke-matrix.shs` = `15/15 codegen_fallback_hits=0`;
  `check-native-seed-parity.shs` = `native_seed_parity=true`. Every fix adds a
  parity case (inline, not via a sub-lane).
- Land via FF-replay onto the `ls-remote` tip; verify with `ls-remote` +
  content-grep. **No branches. No redeploy without explicit user go-ahead.**

Effort key: **S** ≤1 lane/hunk · **M** multi-hunk, one subsystem · **L** cross-cutting
(ABI / cache-format / new lowering path).

## Current audit (2026-07-15)

The original tables remain the historical root-cause/effort record; Current
execution order below supersedes their implementation order. This audit
prevents already landed fixes from being reimplemented and distinguishes
source fixes from executable proof.

| # | Current disposition |
|---|---------------------|
| 1 | Fixed and native-regressed (`e4471d60acb6`). |
| 2 | Push/fill fixed and native-regressed (`58b0f33701fb`, `135bb60cf0e7`, `8205cacec41a`); concat-array forwarding source fix landed and strict default-LLVM + explicit-Cranelift proof added, execution pending. |
| 3 | Scalar-global source fix landed; strict default-LLVM + explicit-Cranelift direct/getter first-read proof added, execution pending. |
| 4 | Enum text-payload source fix landed; strict default-LLVM + explicit-Cranelift callback/match/field-assignment proof added, execution pending. |
| 5 | Subject-enum variant precedence implemented for expression and statement match; focused Rust tests pending execution. |
| 6 | Old two-slot `Any` premise is superseded by the one-word ABI; strict default-LLVM + explicit-Cranelift wrapper-to-extern forwarding proof added, execution pending. |
| 7 | Source implemented at the contained MIR enum-bind owner; strict default-LLVM + explicit-Cranelift proof added, execution pending. |
| 8 | Open; additive `rt_enum_id` runtime/backend surfaces are source-implemented, but the uniform tagged Option ABI remains blocked. Flat text unwrap is implemented but unexecuted. |
| 9 | Capturing and non-capturing stored/passed lambda values implemented with a membership-checked closure ABI; strict hosted/simple-core default-LLVM + explicit-Cranelift proof added, execution pending. |
| 10 | Captured scalar/struct closure storage implemented through the same closure ABI; strict dual-runtime/backend proof added, execution pending. |
| 11 | Fixed by Unit-arm merge suppression and backend void-spill protection. |
| 12 | Source implemented; lifecycle hooks are optional and weak/null-guarded; fresh native-all bootstrap execution pending. |
| 13 | Fail-closed seed compatibility implemented with a stale-cache regression; test execution pending. |
| 14 | Pure-Simple cache scope now includes the running compiler hash; focused runtime test pending. |
| 15 | Seed cache-key source fix and focused regression implemented; fresh executable cache proof pending. |
| 16 | Target-aware global cfg selection implemented across native, driver/JIT, imports, and module loading; AArch64/RISC-V LLVM object regressions added, execution pending. |
| 17 | Module+owner-qualified method identity implemented through imports, HIR, MIR, bootstrap, trait defaults, and static methods; strict LLVM+Cranelift dispatch proof pending. |
| 18 | Pure-Simple Cranelift dynload globals now declare, initialize, load, and store writable scalar data; strict LLVM+Cranelift init/mutation proof pending. |
| 19 | Open/partial; dispatch/spin, compiler backfill/provider slices, and test-only deterministic requested-symbol owner validation are implemented; aggregate final-closure derivation, full cache fingerprint, remaining providers, production selection/link wiring, and strict execution remain. |
| 20 | C-owned host-GPU queue facade and fail-closed archive ownership checks implemented; native queue execution proof remains. |
| 21 | Reduced to the Rust seed parser's inline-continuation consumption bug; inline-first and block-first source fixes plus focused chained-inline regressions are implemented, while regression and real inspector execution remain pending. The pure-Simple parser needed no rewrite. |

---

## Wave 1 — Codegen silent-wrong (highest priority: wrong answers, no diagnostic)

A wrong-but-silent result is the worst failure class; these go first.

| # | Bug | Root cause → fix approach | Site | Effort |
|---|-----|---------------------------|------|--------|
| 1 | `native_untyped_text_eq_and_fused_bool_miscompile` | Untyped (`Any`/dict-derived) text `==` compares handles not contents → never matches; fused `and`/`or` chains mis-lower. Route erased-text `==` through `rt_native_eq`; fix fused-bool short-circuit block wiring. | `expr_dispatch.spl` (Binary eq + bool) | M |
| 2 | `native_untyped_array_push_and_fill_literal` | `.push()` on untyped array is fatal; `[""; N]` fill-literal emits invalid IR. Add `rt_array_push` interception for erased receivers; lower fill-literal via `rt_array_fill`. | `method_calls_literals.spl`, `aggregate_intrinsics.spl` | M |
| 3 | `native_module_var_bool_garbage_init` (P1) | Module-level `var x = false` reads garbage-truthy at startup — initializer not run before first read. Emit a module-init store for scalar bool/int globals (ties to #19). | `bootstrap_globals.spl` | M |
| 4 | `native_enum_text_payload_decimalized` | Enum text payload prints as a decimal pointer — payload typed as int not str. Thread the variant's declared text payload type into the print/`to_text` dispatch. | `switch_operators_calls.spl` | S |
| 5 | `native_const_pattern_lowers_irrefutably` | `case CONST:` match arm lowers as irrefutable (always taken), skipping the equality test. Emit the `rt_native_eq`/`icmp` guard for const patterns. | `expressions.spl` (build_match) | S |
| 6 | `native_any_param_forwarding_corruption` (High) | Forwarding an `Any` parameter corrupts the pointer (tag/box mismatch on pass-through). Preserve the tagged handle across the call boundary; no re-box. | `core_codegen.spl` call lowering | M |
| 7 | `native_codegen_crossmodule_generic_result_u8_erasure` | Imported function signatures already retain concrete `Result<[u8],E>` through HIR and the no-op monomorphization pass; MIR `rt_enum_payload` binding dropped the existing runtime-array marker. Recover the selected Result payload type in `lower_enum_match` and preserve array provenance. | `switch_operators_calls.spl` (`lower_enum_match`) | S |
| 8 | Option ABI pair: `native_try_op_on_option_silent_wrong` + `native_text_option_unwrap_pointer_value` | Flat `i64?` payload `3` collides with the nil sentinel; `?`/unwrap on Option mis-dispatch. Needs a uniform tagged Option handle (`OPTION_ENUM_ID=1`, `Some=0/None=1`), `rt_enum_id` in both runtimes, and declared-type provenance for locals/calls. Design already recorded in the two bug docs. | HIR Optional canon + MIR + runtime | L |

**Note on #8:** blocked on a runnable pure-Simple `native-build` verification gate
(source-only landing cannot prove absence of double-wrapping / payload-3 collision
/ Result regressions). Do this last in Wave 1, with the ABI acceptance matrix from
the bug docs as the gate.

---

## Wave 2 — Unsupported constructs (loud today; real feature gaps)

Currently loud-fail (correct discipline), but block real programs.

| # | Bug | Approach | Site | Effort |
|---|-----|----------|------|--------|
| 9 | `native_first_class_lambda_values_unsupported` | `CallIndirect` through a non-inlined lambda value. Needs a heap closure env + indirect-call lowering (the escaping-closure case the closures2 lane left out). | switch_operators + new closure runtime | L |
| 10 | `native_struct_closure_capture_hang` | Struct-field closure capture hangs the build. Break the cyclic lowering; same closure-env work as #9. | MIR closure lowering | M |
| 11 | `native_if_print_only_arms_alloca_void` | Statement-form `if` with print-only arms emits `%l = alloca void` (invalid IR). Skip the result alloca when both arms are `void`. | `core_codegen.spl` if-lowering | S |
| 12 | `native_runtime_path_optional_lifecycle_rejected` | Native runtime link rejects archives lacking optional lifecycle hooks. Make the hook symbols weak/optional at link. | `native_linking.spl` | S |

---

## Wave 3 — Build cache / identity / link integrity (silent stale-code hazards)

These can link OLD code into a "successful" build — a correctness hazard even
though the compiler itself is right.

| # | Bug | Approach | Site | Effort |
|---|-----|----------|------|--------|
| 13 | `native_build_noncritical_skip_stale_cache_masking` (high) | "non-critical file skipped" links a stale `.o` silently → deployed binary runs code matching no source rev. Make a skip fail the build (or force-recompile), never reuse stale. | native_project pipeline | M |
| 14 | `native_build_cache_omits_compiler_identity` | Cache key omits compiler identity → stale artifacts survive a compiler change. Fold compiler content-hash into the key. | native_project cache | S |
| 15 | `native_object_cache_key_omits_seed_version` (P2) | Same class for the incremental `.o` cache: key omits seed/compiler version. Merge fix with #14 (one cache-key change). | native_project cache | S |
| 16 | `native_cfg_duplicate_global_target_selection` | `@cfg` duplicate globals pick the wrong target. Deterministic cfg target selection. | driver cfg resolution | M |
| 17 | `native_method_cleanup_global_misresolution` | Method-cleanup pass misresolves a global. Fix the symbol lookup scope. | MIR method cleanup | M |
| 18 | `native_dynload_module_var_static_init_dropped` | Dynload build drops static initializers on module-level `var` globals (repro: WM render-event gate). Emit + run the init in the dynload path (ties to #3). | dynload codegen | M |
| 19 | `native_build_stage4_pre_object_spin` | Stage-4 dispatch + strict-link blockers (pre-object spin). Mitigations documented in-doc; finish the strict-link path. | driver stage4 | M |

**#19 production-path note:** Stage 4 executes the verified pure-Simple compiler,
whose `driver_aot_output.spl` calls `llvm_native_link.spl`; Rust
`native_project` validators are test-only prerequisites and are not production
wiring. The exact CLI profile must derive its final requested `rt_*`/`spl_*`
closure after entry-object creation, validate unique archive ownership, and then
order Simple objects → compiler capsule → capability providers → core-C → system
libraries. The current provider inventory covers compiler hooks, time/progress,
SQLite, and memtrack only; GPU/font/dynload, window, HTTP, process/thread,
SMF/CUDA, and other CLI owners remain. Core-C currently overlaps memtrack, raw
`libsimple_native_all.a` selection and allow-multiple-definition are still
invalid for the strict profile, and provider ownership needs a separate link
profile fingerprint rather than changing per-module object keys.

---

## Wave 4 — App/lane-specific (scoped, lower priority)

| # | Bug | Note |
|---|-----|------|
| 20 | `native_engine2d_runtime_queue_symbols` | Engine2D runtime queue symbols missing from the linked runtime — add to the runtime facade export set. |
| 21 | `native_renderdoc_inspector_else_parse` | `Else` parse failure in the RenderDoc inspector source — parser edge case. |

---

## Reclassify / verify-first (not Wave work as-filed)

- `native_build_entry_closure_no_forkwait_deadlock_slow_parse` — self-classified
  **informational**: no deadlock; redirect the residual to parser-perf tracking.
  Do NOT implement an orchestration fix against this premise.
- `native_project_cache_hit_miss_mix_link_input_loss` — status **NOT REPRODUCED**;
  needs a reliable repro before any fix. Park until reproduced.
- `native_sspec_expect_step_stub_host_gpu_lane` — self-reports **fixed** (native
  preprocessed specs link without `expect`/`SIMPLE_DUMP_STUBS` empty). Verify and
  mark Resolved, or reopen with a fresh repro.

---

## Current execution order

The original wave tables above preserve root-cause history; this list supersedes
their implementation order.

1. Run each row's recorded focused/native/parity gate for execution-proof-only
   rows #2–#7, #9–#10, #12–#18, and #20–#21. Native/parity gates wait for a
   valid pure-Simple executable; do not reimplement landed source fixes.
2. Implement #8 as one atomic uniform tagged Option ABI change, including every
   producer/consumer boundary and the full Result-preservation matrix. Do not
   land another partial representation change.
3. Finish #19's aggregate final-symbol closure, complete provider inventory,
   production archive selection/link wiring, and cache fingerprint before its
   strict execution gate.

**Redeploy dependency:** pending native/parity proof and the atomic #8 ABI gate
require a working pure-Simple `native-build` artifact; focused Rust/source-level
regressions can execute independently. Rebuild/deploy remains an explicitly
authorized operation; source status must not be promoted to fixed until its
recorded gate runs. #19 may continue with source-only fail-closed composition
prerequisites, but production enablement still requires strict native proof.
