# Bug-Coverage Audit — 2026-07-18

Read-only audit. Question answered: of the bugs tracked in
`doc/08_tracking/bug/`, is every open item assigned to an agent/lane, or is
something falling through the cracks?

## Method

- `doc/08_tracking/bug/` has ~620 files; 379 were touched in the last ~10 days.
  Of those, 24 carry an explicit `open`/`in-progress` Status line; a further
  handful surfaced as ambiguous (no Status line but unresolved body text) and
  were read directly.
- Cross-referenced every candidate against: `git log --oneline --since=2026-07-07
  origin/main` (2355 commits — the campaign is much larger than the 12 named
  lanes in scope for this audit), `git -C <worktree> log --oneline
  origin/main..HEAD` for all 29 `/home/ormastes/dev/wt_*` worktrees, and the
  named lanes S77/S81–S91/T1/T2.
- `doc/TODO.md` (528 items, auto-generated) and `doc/08_tracking/todo/` were
  checked; the only P1 entry (crypto SFFI `_unwrap_sig`) is **already fixed and
  removed on origin** (`f9b34943859 cleanup(crypto-sffi): remove dead
  _unwrap_sig workaround + stale P1 TODO`) — `doc/TODO.md` itself is stale and
  needs a `bin/simple todo-scan` regeneration.
- `doc/08_tracking/bug/bug_db.sdn` and `bug_report.md` are both stale
  auto-generated artifacts (last meaningful entry 2026-04/06-04) and were not
  used as a source of truth — the individual `.md` files are authoritative.

## Coverage table (candidates actually investigated)

| Bug doc | Severity | Status in doc | Coverage |
|---|---|---|---|
| `be_dom_event_missing_prevent_default_stop_propagation_2026-07-11.md` | — | OPEN (top line) | **STALE — landed** `2f661ec0b66`; doc's own `## Resolution (2026-07-17)` section confirms FIXED. Top Status line never updated. |
| `llvm_aot_function_section_gc_2026-07-17.md` | P0 bootstrap blocker | OPEN — implementation+tests pending | **Partially landed.** `940d2396e27 fix(llvm): emit discardable function sections` (2026-07-17) matches the root cause; doc re-touched 07-18 still lists required prevention tests as undone. Residual = tests only, unassigned. |
| `bootstrap_stage2_empty_mir_bodies_2026-07-05.md` | high | IN_PROGRESS | **Mostly resolved, no owner for the rest.** Doc's own tail: "Both walls are now clear... Next owner: attempt the full redeploy closure build" — no lane currently claims that follow-up. |
| `mcp_full_program_native_codegen_and_arg_extract_2026-06-16.md` | P1 | OPEN (defects C, D remain) | **Split.** Native simple-mcp path already resolved 2026-07-15 per doc's own severity line; defects C (stage4/cranelift full-program) and D (Linux LLVM-18 detection) have no matching commit. PENDING for C/D. |
| S81 rt_string_data EXTERN_DISPATCH | — | (lane) | Fixed locally, unlanded: `c8f1bb85e88` in `wt_clif` (verified not-on-origin). |
| S82 Object/Enum marshal | — | (lane) | Fixed locally, unlanded: `fff67359f28` in `wt_s54` (verified not-on-origin). |
| S83 array test contract | — | (lane) | Fixed locally, unlanded: `cc3aee67bd9` in `wt_repro2` (verified not-on-origin). |
| S84 String bare-field `.len` | — | (lane) | Fixed locally, unlanded: `39a80a4ee85` in `wt_s10` (verified not-on-origin). |
| S86 MODULE_GLOBALS COW gap | — | (lane) | Fixed locally, unlanded: `592ff7d10c6`+`a07560bdd97` in `wt_q_crossmodule`. **Does not resolve** `interp_module_global_stale_read_in_spec_blocks` — doc explicitly says these are different subsystems. |
| S90 rt_dir_walk legacy API | — | (lane, described as "in progress") | Actually has a fix commit already: `dc63d4120a9` in `wt_q_optdyn`, unlanded — more done than the brief implied. |
| S91 rt_string_data cranelift-direct | — | (lane, described as "in progress") | Actually has a fix commit already: `cb82a5875e4` in `wt_q_text_return`, unlanded — more done than the brief implied. |
| S85 MIR serialization | — | (lane) | Genuinely in-progress: `wip` + groundwork-report commits only, in `wt_q_cache`. |
| S77 stage-4 full-CLI build | — | (lane) | Diagnosis-only commit in `wt_s58` ("not a loop, a legitimate 662+ file re-compile"); no fix commit yet. |
| T1 (SSpec system tests) | — | (lane) | `wt_t1` has **zero** unlanded commits — either already landed or not yet started; could not disambiguate without deeper history dig. |
| T2 (unit+integration specs) | — | (lane) | `wt_t2` has **zero** unlanded commits — same caveat as T1. |

## PENDING — no agent assigned

These are open per their own doc content (many re-verified "STILL-REPRODUCES"
as recently as 2026-07-17), and none matched any landed commit, local worktree
commit, or the named S/T lanes.

1. **`nvme_fw_rv64_direct_build_timeout_2026-07-07.md`** — RV64 direct build still exits 143 before producing `build/nvme_fw_rv64.elf`, despite ~70 landed "split rv64 ... cases" refactor commits reducing parse load. Doc's own last line: "do not count this probe as forward RV64 direct-build evidence." Heavily invested, still broken, nobody currently owns closing it. **Next action:** resume the parse-load reduction from the current split point, or profile what's still timing out at the `logic_io_command_cases.spl` boundary.
2. **`cpu_simd_mutable_array_extern_wiring_2026-05-31.md`** — mutable typed-array write-back bridge for `rt_engine2d_simd_fill_u32` still missing; blocks full-frame 8K perf. **Next action:** implement the write-back bridge described in the doc.
3. **`bootstrap_stage4_graph_load_timeout_2026-07-05.md`** (high) — needs `mut`-param + destructuring support in `parse_full_frontend`/HIR let-lowering before the timeout fix is even testable. **Next action:** frontend feature work, not a timeout tweak.
4. **`self_hosted_font_renderer_optional_field_shape_2026-07-11.md`** (P1) — `Engine2D`'s module-global optional `FontRenderer` doesn't retain mutation across calls; zero pixels rendered despite valid face/glyphs. **Next action:** give it a reference-stable owner (boxed/shared renderer) per the doc's own suggestion.
5. **`pure_simple_spipe_docgen_vector_font_spec_crash_2026-07-11.md`** — pure-Simple CLI SIGSEGVs running spipe-docgen on the vector-fonts spec. **Next action:** reproduce in an isolated worktree and fix the docgen owner, per doc.
6. **`js_engine_missing_builtins_regex_promise_prototype_2026-07-11.md`** (medium) — `String.replace(regex,...)` no-op, `Promise` undefined, prototype methods not introspectable. **Next action:** implement the three builtins.
7. **`js_engine_no_dom_bom_globals_2026-07-11.md`** (high) — `JsRuntime` exposes no `document`/`window`/`navigator`/`localStorage`. **Next action:** bridge to existing `browser_engine/script/*` API per doc.
8. **`shared_font_pure_simple_shaping_gap_2026-07-11.md`** — GSUB plan selection/application is the remaining blocker for shared multilingual GPU fonts. **Next action:** implement GSUB application on top of the already-landed run-resolution work.
9. **`draw_ir_window_shadow_clipped_2026-07-13.md`** (TODO 554) — window shadow bounds don't survive the embedded-surface clip. **Next action:** per doc's "Owner fix" section, represent shadow bounds so they survive clipping.
10. **`stage4_deploy_timeout_blocks_release_path_guard_2026-07-08.md`** — stage4 deploy must finish before this guard can be rechecked; likely blocked on the stage3 exit-139 path. **Next action:** diagnose stage4 worker's silent timeout.
11. **`shared_font_req015_deployed_selfhost_segv_2026-07-14.md`** — REQ-015 self-host verification exits 139; explicitly "do not use the Rust seed to close this." **Next action:** fix+redeploy pure-Simple CLI, then rerun 4 listed specs.
12. **`mcp_full_program_native_codegen_and_arg_extract_2026-06-16.md`** — defects C (stage4/cranelift full-program build) and D (Linux LLVM-18 detection) remain per doc's own severity note.
13. **`bootstrap_logging_diagnostics_2026-07-07.md`** (high, IN_PROGRESS) — no matching commit found; status is self-described in-progress but nothing lands against it recently.
14. **`cranelift_seed_missing_sffi_externs_2026-07-16.md`** (medium) — blocked purely on a seed/self-hosted binary redeploy (classic recurring "deploy wall"); doc explicitly rejects a source workaround as churn.
15. **`engine3d_facade_no_vulkan_backend_dispatch_2026-07-03.md`** (P3) — confirmed STILL-REPRODUCES 2026-07-17; `Engine3D.create_with_backend` only ever builds `CpuBackend3D`, no `VulkanBackend3D` field/dispatch exists despite the large volume of *other* Vulkan work landed elsewhere (Engine2D/GPU/fonts).
16. **`interp_option_dict_return_erased_2026-07-16.md`** (medium) — confirmed STILL-REPRODUCES; `-> Dict<K,V>?` erased to nil in the live-interpreted compiler context. (Distinct from the landed `de9de0f779c`/`87f89044030` Dict fixes, which cover `.keys()/.values()` routing and type-annotation generic-arg capture, not this return-erasure path.)
17. **`riscv64_source_qemu_build_requires_llvm_seed_support_2026-06-06.md`** — confirmed STILL-REPRODUCES; needs the Rust seed driver rebuilt with the `llvm` feature enabled.
18. **`interp_module_global_stale_read_in_spec_blocks_2026-07-05.md`** (medium) — doc explicitly distinguishes itself from the S86 `MODULE_GLOBALS` COW fix ("this bug remains open... different subsystems, no shared mechanism").
19. **`iterator_collect_generic_restoration_2026-07-17.md`** — `Iterator.collect` needs HIR/MIR generic-parameter restoration across `List<T>`/`FixedVec<T,N>`/`StaticVec<T,N>`; no matching commit anywhere.
20. **`engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md`** — original nil-command fault is FIXED, but doc's own latest verdict explicitly recommends the new 192MB-heap-exhaustion-from-offscreen-surfaces issue "as the next lane" — nobody has picked that up yet.
21. **`self_hosted_simpleos_target_native_build_crash_2026-07-11.md`** (P0) — extensive multi-day progress through 07-12 (static ELF64 built, `rt_math_pow` gap closed), but the last recorded step is "Verification awaits a fresh libc/sysroot rebuild and capped LLC/LLD relink" — no confirmation it landed, and no current owner.

**Count: 21 pending items** (2 of the 24 open-status candidates were reclassified — `be_dom_event...` to STALE/landed, and `llvm_aot_function_section_gc` and `bootstrap_stage2_empty_mir_bodies` split into "mostly landed, thin residual pending").

## Already landed (examples confirmed by commit match)

- `be_dom_event_missing_prevent_default_stop_propagation` → `2f661ec0b66` (doc STALE, needs Status line update).
- Dict `.keys()/.values()` routing → `de9de0f779c`; `Dict<K,V>` generic-arg capture → `87f89044030`.
- LLVM AOT discardable function sections → `940d2396e27` (code landed; doc's required regression tests still open, see table above).
- crypto SFFI `_unwrap_sig` TODO → `f9b34943859` (TODO.md itself is stale).
- The bulk of `nvme_fw_rv64_*` "split ... cases" refactor commits (~70) are landed but did **not** close the underlying timeout (see PENDING #1).

## Fixed locally, awaiting landing (with SHAs)

All verified NOT ancestors of `origin/main` via `git merge-base --is-ancestor`:

| Lane | Worktree | SHA(s) |
|---|---|---|
| S81 | wt_clif | `c8f1bb85e88` |
| S82 | wt_s54 | `fff67359f28` |
| S83 | wt_repro2 | `cc3aee67bd9` |
| S84 | wt_s10 | `39a80a4ee85` |
| S86 | wt_q_crossmodule | `592ff7d10c6`, `a07560bdd97` |
| S90 | wt_q_optdyn | `dc63d4120a9` (+ S87 audit commits `f49aa698544`,`18e471147f0`,`fa2d7abd90e`) |
| S91 | wt_q_text_return | `cb82a5875e4` |
| (unnumbered, #185/#187/#188) | wt_s11 | `7e8da29b025`, `ed1de4746a8`, `1fb24be0509` |
| (unnumbered, #186) | wt_s21 | `d3ae328ee58` |
| (unnumbered, task #170) | wt_r_fn_type | `0d5cc55ead6`, `f840c4a0363` |
| (unnumbered) | wt_s55 | `fd23e3d5a2c` |
| (unnumbered) | wt_seedfix | `ac4a2391d27` |
| (unnumbered) | wt_s_option_map | `2c6a05c1dd7`, `3e83a986c8a` |
| (unnumbered, --threads plumbing) | wt_land, wt_s_mixed_cmp | `ba95d9f90ff`/`98e51824db1` |
| S85 (WIP, not done) | wt_q_cache | `d898c866929`, `844a3c7069f` |

`wt_fix`, `wt_p1`, `wt_p2`, `wt_r_cl_statics`, `wt_s22`, `wt_s56`, `wt_t1`,
`wt_t2` show zero unlanded commits — clean, either idle or already merged.

## Note on scope

The campaign memory (`project_bugfix_campaign_landwar_2026-07-17.md`) shows
far more numbered lanes in flight (S23–S91+, dozens of bug-number tasks like
#99/#170/#172/#178/#185–191) than the 12 named in this audit's brief. This
report only reconciles the 12 named lanes plus whatever surfaced from the
recently-touched bug-doc scan; it is not a full inventory of the entire
parallel campaign.
