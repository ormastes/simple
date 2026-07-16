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
| 1 | Text equality was native-regressed (`e4471d60acb6`); shared MIR `and`/`or` now uses true short-circuit CFG lowering, entry-hoisted merge slots, and compatible textual-LLVM SSA repair. Focused dual-backend proof is present and pending execution. |
| 2 | Push/fill fixed and native-regressed (`58b0f33701fb`, `135bb60cf0e7`, `8205cacec41a`); concat-array forwarding source fix landed and strict default-LLVM + explicit-Cranelift proof added, execution pending. |
| 3 | Scalar-global source fix landed; strict default-LLVM + explicit-Cranelift direct/getter first-read proof added, execution pending. |
| 4 | Enum text-payload source fix landed; strict default-LLVM + explicit-Cranelift callback/match/field-assignment proof added, execution pending. |
| 5 | Subject-enum variant precedence implemented for expression and statement match; focused Rust tests pending execution. |
| 6 | Old two-slot `Any` premise is superseded by the one-word ABI; strict default-LLVM + explicit-Cranelift wrapper-to-extern forwarding proof added, execution pending. |
| 7 | Source implemented at the contained MIR enum-bind owner; the cross-module `Result<[u8], E>` fixture now routes both Ok and Err through `?`, with LLVM and Cranelift execution scheduled on FreeBSD x86_64 plus AArch64/RISC-V QEMU. Execution is pending. |
| 8 | Open/safer; typed local/direct-call/resolved-method Option `?` fail-closed provenance and additive `rt_enum_id` surfaces are source-implemented. Hosted Linux/macOS/Windows and FreeBSD x86_64 schedule annotated/direct loud-fail checks under LLVM and Cranelift; ARM32 LLVM and Windows ARM64 LLVM/Cranelift add target-directed compile-refusal/no-object checks. Execution is pending, resolved-method coverage is source-only, and unresolved late dispatch remains unguessed. The uniform tagged Option ABI remains blocked; flat text unwrap is implemented but unexecuted. |
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
| 19 | Open/partial; dispatch/spin, compiler backfill/provider slices, POSIX/macOS/BSD and Windows core-C process-timeout ownership, canonical core-C HTTP tuple ownership, private vendored font symbols, conditional pure-C dynamic-loader ownership with shared LLVM/Cranelift hosted-platform regression, pure-Simple aggregate final-request derivation, deterministic unique-owner archive selection, canonical link-profile fingerprint input, cross-platform candidate-path/native-all discovery and hosted transitive link policy, explicit-entry dispatch, and a fail-closed barrier against ordinary-link fallthrough are source-implemented. Hosted Windows candidate validation now case-normalizes relative `.a`/`.lib` paths while Unix remains case-sensitive. Remaining providers, production archive hashing/digest/cache wiring, production inventory/link selection, and strict execution remain. The LLVM-configured Windows job now selects the existing strict LLVM/Cranelift `dynload_tagged_text` proof and forbids backend XFAIL; execution is pending. |
| 20 | C-owned host-GPU queue facade and fail-closed archive ownership checks implemented; native queue execution proof remains. |
| 21 | Rust-seed inline-continuation fix and focused chained-inline regression are verified (`simple-parser` control-flow test: 19 passed); real inspector execution remains pending behind the unrelated pure-Simple `rt_cli_arg_count` bootstrap failure. |

## Verification update (2026-07-16)

The host-GPU checker had seven unresolved merge-conflict blocks and could not
parse. Those blocks were resolved in the checker, including the TCG/native
QEMU argument distinction and runtime-evidence predicates. `bash -n` now passes.
The checker self-test still stops at pure-Simple candidate admission: the
candidate native-build probe is killed before producing its proof artifact.
This remains an execution blocker; no host-GPU or QEMU PASS is claimed until
that admission failure is fixed and the self-test completes.

Hosted native linking now fails closed before compiling the C runtime or entry
shim when an explicit target architecture or OS differs from the compiler
host. Host/unset and exact hosted targets remain supported; SimpleOS keeps its
specialized link lanes. Real hosted cross-linking remains open until one
resolved target compiler/sysroot is threaded through both C compilation steps.

Target-qualified `asm match`/`asm assert` lowering no longer assumes
`x86_64-linux-gnu` with LLVM 15. The driver now creates one immutable target
context from the requested triple, normalized host fallback, effective backend,
and cached LLVM tool version, then threads it through normal, bootstrap, and
nested-lambda MIR lowering. Linux, macOS, Windows, FreeBSD, x86/x86_64,
ARM/AArch64, and RISC-V normalization regressions are recorded. LLVM remains
the default; Cranelift remains available only when selected explicitly. Because
Cranelift exposes no version discovery surface yet, version-qualified Cranelift
asm fails diagnostically instead of comparing against a fabricated version. Runtime
  execution proof is pending the repaired staged pure-Simple CI under the
  verification contract above; the historical exit 139 has no retained current
  reproducer.

FreeBSD QEMU `--full` now runs the complete 15-case default-LLVM native-entry
matrix after the focused explicit-Cranelift probe and requires zero codegen
fallback hits. Its cross-module Result control now covers Ok payload extraction
and Err propagation through `?` under both backends. The same fixture is wired
for AArch64/RISC-V QEMU; execution is pending.

The existing Linux x86_64 LLVM bootstrap CI leg now enables canonical Stage 5,
which builds both pure-Simple MCP servers and runs their fresh-artifact
initialize/list/call smoke. Other host/backend legs still skip that duplicate
build. The pure-Simple architecture job now requires a default-LLVM ARM32
ELF32/ARM relocatable object from the staged compiler and proves explicit
Cranelift rejects ARM32 without leaving an object. AArch64 and RISC-V retain
their dual-backend QEMU execution gates; hosted ARM32 linking remains
explicitly unsupported.

Windows x86_64 LLVM CI now also uses its freshly staged pure-Simple compiler
to emit an `aarch64-pc-windows-msvc` COFF object with the default backend and
requires `IMAGE_FILE_MACHINE_ARM64`. The legacy Windows ARM64 job that only
inspected the repository's Linux binary has been removed.

Cranelift AOT source now sends the exact requested target triple from the
pure-Simple target-context owner through a new ABI entrypoint; the legacy
architecture-code export remains intact for staged/bootstrap compatibility.
Invalid explicit triples fail module creation rather than falling back to the
host. The Windows staged lane separately requires explicit Cranelift to emit an
ARM64 COFF object; this is object-format coverage only, not Windows ARM64
linking or execution coverage.

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

**#19 production-path note:** Before the explicit-entry dispatch fix,
`bootstrap_main.spl` sent Stage 4 through Rust `rt_native_build`; the
pure-Simple `driver_aot_output.spl` → `llvm_native_link.spl` path was therefore
not production wiring for that bootstrap shape. Current source now routes the
canonical Stage4 one-binary `--entry src/app/cli/main.spl` through the in-process
pure-Simple project driver without a silent seed retry or raw native-all path;
executable proof remains pending. Rust `native_project` validators
remain test-only prerequisites. The exact CLI profile now derives its final requested
`rt_*`/`spl_*` closure after entry-object creation; it must next validate unique
archive ownership and order Simple objects → compiler capsule → capability
providers → core-C → system libraries. The current provider inventory covers
compiler hooks, time/progress, SQLite, memtrack, and POSIX/macOS/BSD plus Windows
process-timeout source ownership. The LLVM-configured Windows job now runs the focused strict-dual
dynamic-loader case through the staged compiler; its first CI execution remains
pending. GPU/font/dynload,
window, HTTP, remaining process/thread,
SMF/CUDA, and other CLI owners remain. Core-C currently overlaps memtrack, raw
`libsimple_native_all.a` selection and allow-multiple-definition are still
invalid for the strict profile, and provider ownership needs a separate link
profile digest/cache namespace from the canonical input rather than changing
per-module object keys.

---

## Wave 4 — App/lane-specific (scoped, lower priority)

| # | Bug | Note |
|---|-----|------|
| 20 | `native_engine2d_runtime_queue_symbols` | Runtime SFFI now registers `rt_host_gpu_queue_emit_payload_text` with a focused ABI regression; end-to-end native Engine2D queue execution remains pending. |
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
3. Finish #19's provider inventory, production archive selection/link wiring,
   and canonical-input digest/cache namespace with invalidation proof before
   its strict execution gate.

**Redeploy dependency:** pending native/parity proof and the atomic #8 ABI gate
require a working pure-Simple `native-build` artifact; focused Rust/source-level
regressions can execute independently. Rebuild/deploy remains an explicitly
authorized operation; source status must not be promoted to fixed until its
recorded gate runs. #19 may continue with source-only fail-closed composition
prerequisites, but production enablement still requires strict native proof.
