# GPU Frontend Offload — Staged Plan

**Date:** 2026-09-05 (updated 2026-09-06) · **Lane:** `.spipe/gpu_frontend_offload`
**Design:** `doc/05_design/compiler/frontend/gpu_frontend_offload_switch_design.md`
**Research:** the two 2026-09-01 docs under `doc/01_research/compiler/parser/`
plus the 2026-09-05 gap doc.

## Wave 0 — the switch — **COMPLETE, merged**

Landed as PR #377 (`a4673923076`) and PR #385 (`3aa737b8b54`).

| ID | Task | Owner path | Exit evidence |
|---|---|---|---|
| GFO-001 | Pure resolver + profile/decision/receipt helpers | `structural_contracts/frontend_offload_switch.spl`, `__init__.spl` export | DONE — `frontend_offload_switch_spec` 20/20; sabotage bites (env-beats-cli → 1 failed; pre-fix contract → 2 failed) |
| GFO-002 | Driver env read, decision, fail-closed error, dtrace + warm-receipt rows | `80.driver/driver_source_pipeline_parsing.spl`, `app/cli/native_build_warm_receipt.spl` | DONE — `frontend_offload_driver_unit_spec` 6/6; sabotage (`available=true`) bites. **Live driver behaviour unverified on this host** — see Deferred |
| GFO-003 | CLI flags set the env vars (and are not forwarded onward) | `src/app/run/main.spl`, `src/app/cli/native_build_main.spl` | DONE — env_set only; both flags stripped from the forwarded argv in `run` (2026-09-05) and in the `native-build` worker (2026-09-06) |
| GFO-004 | Manual + wiki + guide | `doc/06_spec/...`, feature-expert skill, `doc/07_guide/compiler/frontend/frontend_offload_switch.md` (+tldr) | DONE — 3 manuals `0 stubs`; generated with the **main-tree** docgen (the committed one fails `E1002 spec_kw_line`) |

Wave 0 did not edit any peer-dirty file (`10.frontend/treesitter/*`, `core/lexer*.spl`,
`structural/parse/contracts.spl|dialect.spl`, `structural_adapter/`, `spipe_docgen/*`).

### Landed incidentally (found by this lane, fixed in the same PRs)

| ID | Item | Evidence |
|---|---|---|
| GFO-I1 | `auto` rejected as a named-argument label (seed parser) — `TokenKind::Auto` added to the label match **and** `is_likely_named_arg` | `parser_auto_contextual_keyword_spec` 3/3 on the rebuilt seed, parse error on the pre-fix seed; generalization `parser_contextual_keyword_named_arg_spec` 8/8. Bug record CLOSED |
| GFO-I2 | aarch64 build break on `[i8; N]` name buffers where `c_char == u8` | `interpreter_extern/gpu.rs:1370` fixed in #377 (its callee is a locally-declared `*mut i8` fn pointer, so the read-side cast is the right fix there; default seed build verified). **Class closed 2026-09-06** at the three `extern "C" cuDeviceGetName` sites — `runtime/src/cuda_runtime.rs:1100,1555` and `gpu/src/backend/{cuda,rocm}.rs:298,268` — by typing the buffer `[0 as std::os::raw::c_char; 256]`, which fixes the **write** side (`as_mut_ptr()`) that a read-side cast alone leaves broken. Proof: `cargo check -p simple-runtime --features cuda` failed with 2×E0308 before and passes after — i.e. the runtime crate never compiled with `--features cuda` on aarch64. `gpu/src/backend/*` carries the identical change **unverified**: `simple-gpu` is not a workspace member (`cargo check -p simple-gpu` → "no such package"; standalone → "believes it's in a workspace when it's not"), so it cannot be compiled from this tree at all — worth its own follow-up |

## Deferred — not verifiable on this host (do not read as done)

Recorded with resume commands in `.spipe/gpu_frontend_offload/state.md`.

| AC | Unproven | Prerequisite |
|---|---|---|
| AC-3 | live compile failure under `require-requested` (only the pure twin + decision fn are exercised) | a deployed **self-hosted** `bin/simple`; the Rust seed never executes the pure-Simple driver |
| AC-5 | live `dtrace` receipt; warm rows inside a real `native-build` identity | same |
| AC-5 | `deterministic_hash` parity between `off` and `on+allow-cpu` | same |
| AC-1 | `simple.sdn frontend.offload*` as an actual source (resolver slot is tested with injected text) | GFO-005 below |
| AC-6 | integration manual counts the two `skip()` cases as active (docgen counts statically) | committed-docgen fix |

## Waves 1+ — blocked on the peer `parser_framework` landing (contracts v2)

Blocker re-verified 2026-09-06 at `origin/main` `c972fd643da`: the structural-parse
executors are still Wave-1 stubs (`action_sink.spl`, `runtime.spl`,
`auto_profile.spl` carry unsupported/not-implemented markers),
`src/compiler/10.frontend/structural_adapter/` does not exist, and
`.spipe/parser_framework/state.md` reads `impl-in-progress`.

Mapped to the research plans (GFPU-xxx = doc 1, GPU-PARSE-xxxx = doc 2):

| Wave | Content | Blocked by |
|---|---|---|
| 1 | contracts v2 + one typed mode enum (GFPU-100..106 / GPU-PARSE-01xx); `gpu_parse_available` becomes real admission; **GFO-005** read `frontend.offload*` from `ProjectContext` (`80.driver/project.spl` `_sdn_text_at`) and forward to `driver_frontend_offload_switch` | peer landing |
| 2 | CPU work table + reason registry + `frontend-work` audit CLI (doc 2 §10, GFPU-800/805) | Wave 1 |
| 3 | SIMD fused UTF/classify/opaque masks over `simd_text_sffi` + `runtime_simd_utf8.c` (GFPU-500..503) | Wave 1 |
| 4 | GPU UTF/lex/structure/token/region stages on `compute_exclusive_scan` ports (GFPU-600..606) | Wave 1, gpu lanes |
| 5 | GPU local parse + Parsed HIR; CPU global names + recovery (GFPU-700..804) | Waves 2–4 |
| 6 | evidence-gated `auto` (≥1.5× median, ADR-OFF-6), resident mode (GFPU-1100..1104) | Wave 5, `gpu_mmu` |

Sosix host-proxy access for CUDA/Vulkan/Metal backends is owned by the sosix
lane; Wave 4 consumes its interface and does not design it.

## Open follow-ups (not blocked, not yet owned)

- **GFO-006 — deployed-seed identity gate.** The shared `bin/release/<triple>/simple`
  was replaced twice (2026-09-05 21:42, 2026-09-06 09:39) by a build predating
  #377. While it was deployed, `check-main-test-runnable-push` failed its own
  selftest with "the clean worktree already fails with a parse diagnostic" —
  this parse breakage wearing a different mask. A `P(auto: true)` probe (or any
  positive capability probe) in whatever gate admits a deployed seed would name
  the cause directly. See `.claude/rules/bootstrap.md` on binary identity.
- **GFO-009 — `frontend_offload_profile` has zero production callers.** It builds
  the `CompilerOffloadProfile` the Wave-1 per-stage dispatcher will need, and is
  covered by a spec, but nothing in `src/` calls it. Either wire it when Wave 1
  lands or delete it; today the design's "resolves into `CompilerOffloadProfile`"
  is true of the decision path only.
- **GFO-008 — `simple-gpu` is not in the cargo workspace.** `src/compiler_rust/gpu/`
  declares `version.workspace = true` but is absent from the workspace `members`,
  so it compiles in no lane here: `cargo check -p simple-gpu` reports no such
  package, and a standalone `--manifest-path` check errors with "current package
  believes it's in a workspace when it's not". Any defect in its CUDA/ROCm
  backends is therefore invisible to every gate, which is how the `c_char` break
  survived there. Either add it to `members` or drop the workspace inheritance.
- **GFO-007 — receipt honesty for `auto`.** `OffloadDecision.requested` reports
  `cpu_reference` for an `auto` request, so the receipt line distinguishes `off`
  from `auto` only by `reason=`. Harmless today; revisit when Wave 6 makes
  `auto` a real selection.

## Gates

- Push tier: unit spec green via `bin/simple test <spec> --no-session-daemon`
  with a `Results:` line; `scripts/audit/direct-env-runtime-guard.shs --working` PASS;
  no new raw `rt_*` outside owner modules.
- Landing: PR only — `main` is ruleset-protected (`Code Idiom & Structural Ratchet
  Gates` + `SPipe Self Review Admission`, no bypass). Note two gates are red at
  `origin/main` itself (`check-rt-dual-implementation-ratchet`,
  `check-runtime-source-list-parity`) and are unrelated to this lane.

<!-- sdn-diagram:gpu-frontend-offload-plan -->
```sdn
wave0: {switch, driver, cli, docs} -> MERGED #377 #385
deferred: {ac3_live, ac5_receipt, ac5_hash_parity, ac1_config, ac6_manual} -> needs self-hosted binary
wave1..6: {contracts_v2, work_table, simd, gpu_stages, local_parse, auto_resident}
blockers: [parser_framework impl-in-progress, gpu_mmu, sosix host proxy]
followups: [seed_identity_gate, auto_receipt_honesty]
```
