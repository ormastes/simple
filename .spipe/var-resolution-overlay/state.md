# Feature: var-resolution-overlay

## Raw Request
"spipe skill dev, refactor out platform env specific logic in same interface,
and configurable deep research refactor simple, os, libs, ui." Refined by the
user into a concrete spec: a resolver-only `var/` variant overlay selecting
platform / hardware / library / renderer implementations via SDN config + module
resolution + DI profiles, with **no new language grammar**.

## Task Type
feature (compiler / module_resolution) + related lib cleanup

## Refined Goal
Add a resolver-only variant overlay (placeholder name `var/`) so source code
imports stable module names while SDN config selects the active
platform/hw/lib/renderer implementation. No grammar changes (`var` stays a
keyword; `use var.*` rejected). Mirror Rust + self-hosted Simple resolvers and
close the pre-existing cache-key parity gap.

## Docs (Phase 1 — DONE)
- Research: `doc/01_research/local/var_resolution_rules.md`
- Requirements/spec (verbatim): `doc/02_requirements/feature/var_resolution_rules.md`
- Plan: `doc/03_plan/compiler/module_resolution/var_resolution_plan.md`
- TODO Phase 2: `doc/04_architecture/compiler/module_resolution/var_resolution_rules.md`,
  `doc/05_design/compiler/module_resolution/var_resolution_rules.md`

## DECISION (resolved)
Root name `var/` collides with git-tracked FHS runtime-state data
(`var/lib/simple_portal/`, `var/lib/web_stack_sample/sample.sdn.wal` — a LIVE
write-ahead log, must not move). Only the on-disk *directory root* collides; the
`var:` / `--var` / `SIMPLE_VAR_*` / `E-VAR*` vocabulary collides with nothing.
**Resolved: overlay on-disk root = `variants/`** (the name the Rust resolver
already references → satisfies H1), vocabulary unchanged. See research §4b.

## DESIGN-PHASE FLAGS (non-blocking)
- Confirm the exact root `stdlib_variant.rs` joins `variants/` to, so the overlay
  reuses that mechanism rather than paralleling it.
- DI selects variants at BUILD time (factory module resolved during compilation),
  so `di.profile.var_profile` is a build-time selector, not runtime. Clarify in
  the design doc; §8's "DI picks the variant" wording is muddled.

## Grounded facts (verified)
- Resolvers: Rust `src/compiler_rust/compiler/src/module_resolver/` (resolve()
  resolution.rs:464, seam :579, cache key hashes `active_simd_tier_name()`);
  Simple `src/compiler/99.loader/module_resolver/` (resolve() resolution.spl:20,
  seam :67-68, cache key `"segments;from_file"` — NO tier → parity gap).
- DI: `config/di.sdn` + `src/compiler/00.common/di_config.spl`; DI bypasses the
  resolver (di.spl:157), so variant selection happens at factory-module load.
- `var/__init__.spl` should use a minimal line-based SDN read (like di_config.spl)
  to avoid a resolver→sdn-parser bootstrap cycle.
- `var` keyword = `KwVar` lexer_types.spl:25. Both @ and #[] tag systems exist.

## Hardening decisions
H1 unify with existing `variants/<simd_tier>/` · H2 bootstrap-safe manifest read ·
H3 DI by profile not path · H4 parity is acceptance (close Simple cache gap) ·
H5 fail closed (E-VAR001–008, tighten cfg_detect_os/arch silent "unknown").

## Phase 3 — model + reader landed, all green
- `src/compiler/99.loader/module_resolver/var_resolution.spl`:
  - model (`VarGroup`/`VarManifest`/`VarSelection`);
  - candidate-root ordering (`var_candidate_roots`, selected-before-default,
    group-order tiebreak, dotted-group → nested dir);
  - fail-closed validation (`var_validate` → E-VAR001..004);
  - **bootstrap-safe line reader** (`var_parse_manifest`, H2 — no full SDN parser).
- `variants/__init__.spl` — canonical on-disk manifest (4 groups: platform/hw/
  lib.crypto/ui.renderer). Parses end-to-end: groups=4, 0 validation errors,
  ui.renderer→`variants/ui/renderer/metal`.
- `test/01_unit/compiler/module_resolver/var_resolution_spec.spl` — **9/9 PASS**
  (170ms): dotted-dir, full root ordering, default-omission, E-VAR001..004,
  and manifest-text round-trip driving validation + ordering.
- Filed `doc/08_tracking/bug/sspec_matcher_to_equal_zero_falsy_2026-06-29.md`
  (`expect(0).to_equal(0)` mis-reports 0 as falsy; worked around via bool).

## Closed side-quest
Tier `platform/` triplication dedup (config→common) was an orthogonal cleanup;
the in-flight unverified shims were **reverted** (tier config.spl back to
identical md5 0cf511d4). Re-open as its own lane later if wanted; not part of this.

## Pure-logic layer COMPLETE (14/14 spec PASS)
- ✅ manifest model + bootstrap-safe line reader (`var_parse_manifest`, H2)
- ✅ candidate-root ordering (`var_candidate_roots`)
- ✅ fail-closed validation (`var_validate`, E-VAR001..004)
- ✅ active-selection precedence (`var_resolve_selections` + `VarSources`):
  CLI > env > config profile > select_default > host-detect (auto) > default
- ✅ SPipe skill section (`.claude/skills/spipe.md` § Var-resolution lanes)
- ✅ canonical `variants/__init__.spl` parses end-to-end

## Phase 4 — Simple resolver hook WIRED (safe-by-default)
- `types.spl`: ModuleResolver gains `var_roots: [text]` + `var_fingerprint: text`
  (both default empty → overlay inactive, ZERO behavior change for existing
  builds) + `moduleresolver_with_var_roots(roots, fingerprint)` setter.
- `resolution.spl`: cache key now `segments;from_file;var_fingerprint` (closes the
  Simple parity gap, E-VAR007); var-root search inserted at the seam (after
  relative, before stdlib), looping `var_roots` via the existing `resolve_from_base`
  — crate.* excluded.
- `var_module_candidates()` — pure ordered candidate-path expansion (single source
  of truth for precedence; backs `simple var resolve` preview + the hook).
- Fixtures `test/.../fixtures/variants/lib/crypto/{openssl,default}/...` + 3
  real-filesystem spec cases prove precedence: absent mbedtls skipped → openssl →
  default → none. **Spec now 17/17 PASS.**

## Verification status (honest)
- ✅ Pure chain (manifest→selection→candidate roots→validation) + real-file
  precedence: 17/17 in interp/`bin/simple test`. Source parses, type-checks, runs.
- ⏳ Full `resolve()` through the live hook can't run in the interpreter (pre-existing
  interp gaps: `text.clone()`, `rt_path_parent` extern absent — both work in the
  compiled binary). Hook is additive + safe-by-default so it cannot regress
  existing resolution unbuilt.
- ❌ `bin/simple build bootstrap` to deploy the change: **Stage 1 FAILED** —
  seed `native-build --source src/app --timeout 180` crashed with `Compile failed
  (exit None)`, NO compile diagnostic referencing any file. This is the repo's
  pre-existing native-build fragility (cf. recent commits on native-build worker
  timeouts / entry-closure scoping), independent of this change: the resolver
  source compiles+runs via the standard path and the edits are inert by default.
  `bin/simple` was NOT replaced (stage1 failure → no deploy); spec still 17/17.
  Binary-level proof is blocked on that separate native-build bug.
- ✅ **DIFFERENTIAL PROOF (this change exonerated):** reverting the resolver edits
  to a CLEAN tree and re-running the exact Stage 1 command STILL segfaults
  (exit 139, core dumped) — identical failure. The blocker is a pre-existing
  native-build segfault, NOT this feature. Filed
  `doc/08_tracking/bug/native_build_src_app_segfault_bootstrap_stage1_2026-06-29.md`.
  Edits restored + verified after the differential.

## Phase 5 (partial) — config reader landed
- `config/var.sdn` (dev/prod/mac_metal profiles) + `var_config_selections(source,
  profile_override)` (bootstrap-safe line reader): active profile + `--var-profile`
  override → `[VarSelection]`. **Spec now 21/21 PASS.**
- COMPLETE configurable chain, tested: config → selections → VarSources →
  precedence → candidate roots → module candidates → real-file resolution.
- Remaining Phase 5: CLI flag plumbing (`--var k=v`, `--var-profile`) + env
  `SIMPLE_VAR_*` reads + `simple var {list,check,roots,resolve}` (resolve uses
  var_module_candidates). These need the driver/CLI layer + a deploy to matter.

## Rust resolver parity DONE (H4) — committed
- `bin/simple` is the cargo-built Rust compiler (54.7 MB == target/release/simple),
  so REAL resolution uses the Rust resolver. Mirrored the hook there:
  `module_resolver/types.rs` ModuleResolver +`var_roots` + `with_var_roots()`
  (inert default); `resolution.rs` Strategy 0 searches var_roots after relative,
  before stdlib, via resolve_from_base. No Rust resolution cache → no fingerprint
  needed there. **`cargo check -p simple-compiler` clean (15s).** Committed pmy 3913.
- Hook now source-complete + compile-verified in BOTH resolvers (Simple 21/21 +
  Rust cargo-check).

## Next steps (for a LIVE binary demo)
1. CLI glue: populate var_roots from config/var.sdn + manifest + host detect, call
   `with_var_roots` (Rust driver) / `moduleresolver_with_var_roots` (Simple). Until
   this exists, var_roots stay empty so the overlay is inert even when deployed.
2. Deploy: `cargo build --release -p simple-driver` + copy to bin/simple — POLICY
   note (bootstrap.md): bin/simple should be self-hosted; current one is already
   the Rust binary. Self-hosted deploy needs bootstrap, blocked by native-build
   segfault. Redeploy affects all parallel sessions → user decision.
3. `simple var {list,check,roots,resolve}` (resolve uses var_module_candidates) +
   DI var_profile + LSP + E-VAR005/006/008.
4. os/libs/ui variant migration — user-gated separate lanes.
