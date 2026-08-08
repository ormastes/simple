# Feature: simple_feature_module (SFM / .sfm)

## Raw Request
> add Simple Feature Module glossary.md and impl sfm and related sample sfm and example usages.
> embedding smf, primary smf format. but .sfm
> support native, loader, script app. web app. mobile app
> Fornt end (UI) and Back end(DB/HW) are exposed
> UI, gui, tui, arg parser. are linked to app
> DB linked
> Dependency Injection to support how link them to app
> not only front end but also layers expose with di/aop for authorization
> it should have special security level unlike other sfm
> make sample arg parsing using app
> log level changer sfm
> login app for web app.
> version control support sfm
> let simple and others to use simple sfm infra
> let it use VERSION.md during build.
> add args parser when native app
> ui app Help/Info menu
>
> (follow-up) update doc and spipe skill also

## Clarifications (from user, 2026-06-04)
- **Scope:** Everything in one pass (full request).
- **Format:** `.sfm` is the *primary* feature-module format and *embeds* the existing
  SMF binary as its code payload; `.sfm` adds a feature manifest (front-end/back-end
  exposure, DI wiring, security level) on top of SMF.
- **Doc/skill updates (all four):** glossary.md + `_tldr.md`; architecture + design docs;
  update the SPipe skill so the workflow can produce/consume `.sfm`; document VERSION.md
  build wiring (create VERSION.md if absent).

## Task Type
feature

## Refined Goal
Introduce **Simple Feature Module (SFM, `.sfm`)** — a primary feature-module container that
embeds an SMF code payload and adds a feature manifest declaring exposed front-end (UI:
gui/tui/arg-parser) and back-end (DB/HW) layers, their dependency-injection/AOP wiring for
authorization, and a per-module security level — together with a reusable SFM runtime
(write/read/load) usable across native, loader, script, web, and mobile app targets, plus
sample SFMs (arg-parser app, log-level changer, web login, version-control), VERSION.md
build integration, glossary/architecture/design docs, and an updated SPipe skill.

## Acceptance Criteria
(see arch.md / spec files for the full AC-1..AC-16 list — preserved verbatim in research/arch docs)

## Phase
implement-wave1-done

## Log
- dev: Created state file with 16 acceptance criteria (type: feature).
- research: Full brief at `.spipe/simple_feature_module/research.md` (EMBED option resolved).
- arch: Full doc at `.spipe/simple_feature_module/arch.md` (modules, interfaces, byte layout).
- spec: Specs at `test/03_system/feature/sfm/` (codec, di_authz, loader_profiles, samples) + probe.
- NOTE: `.spipe/simple_feature_module/` was removed by a concurrent process during research,
  arch, AND implement phases. state.md reconstructed each time from in-context content;
  research.md / arch.md may need re-restoring from the orchestrator if still missing on disk.

### 5-implement-wave1

**Files created (Wave-1 vertical slice):**
- Core lib `src/lib/nogc_sync_mut/sfm/`: `manifest.spl`, `codec.spl`, `container.spl`,
  `loader.spl`, `di_bridge.spl`, `authz.spl`, `version.spl`.
- Samples: `src/app/sfm_samples/arg_parser/{arg_parser_layer,main}.spl` (AC-7),
  `src/app/sfm_samples/reuse_consumer/consumer.spl` (AC-13).
- `VERSION.md` (repo root, `0.1.0`, first non-`#` line is the version).

**GATE — AC-1 byte round-trip probe (actual output):**
`SFM-ROUNDTRIP: PASS`
(`bin/release/aarch64-apple-darwin-macho/simple run test/03_system/feature/sfm/sfm_roundtrip_probe.spl`)

**Spec results (run via `bin/simple run` AND `bin/simple test` — identical, both execute it-blocks here):**
- `sfm_loader_profiles_spec.spl`: 6/6 PASS (genuinely green).
- `sfm_codec_spec.spl`: 6 fail — 4 are pre-existing `to_be_true` matcher limitation,
  2 are pre-existing var-in-tuple-match-arm scoping limitation (`variable 'i'/'second' not found`).
- `sfm_di_authz_spec.spl`: 9 fail — ALL the pre-existing `to_be_true` matcher limitation.
- `sfm_samples_spec.spl`: stays RED (log_level/web_login/vcs/help_info + log.spl are later waves).

**Limitations confirmed pre-existing (discriminated, NOT SFM defects):**
- `to_be_true`/`to_be_false` error under interpreter: reproduced in unrelated
  `test/02_integration/rendering/simd_parity_spec.spl`.
- `variable not found` for a `var` declared inside an `Ok((a,b))` tuple-match arm in an
  it-block: reproduced in a minimal standalone spec (non-SFM literal tuple).
- The codec logic these red tests assert (byte-exact SMF preservation + re-encode idempotence)
  is directly proven by the GREEN probe; AC-3/4/5 allow/deny/missing/ordinary-ungated logic
  proven by a standalone authz probe (denial Err is the authz message, not "no layer registered").
- File FFI path (write_sfm_file→read_sfm_file) proven by a standalone file probe.

**Deviations from arch.md (with reason):**
1. Codec uses **u32-length-prefixed UTF-8 strings** (not fixed-ASCII) so arbitrary
   name/version/role/entry round-trip exactly; decode does UTF-8 in pure Simple because
   `rt_bytes_to_text` does NOT round-trip Simple-constructed `[u8]` (FFI marshalling). Encode
   side `rt_text_to_bytes` is fine (verified).
2. `rt_file_read_bytes` declared `-> [i64]?` and unwrapped — interpreter wraps SFFI `[i64]`
   returns as `Option::Some([...])` (the known signature_sffi hazard). Did NOT redeclare `->[u8]`.
3. `resolve_layer` returns `Ok(layer)` (dropped `as Any` — "cannot cast object to Any").
4. `register_layers` wires in `new_sfm_container` constructor locals (fn-arg mutation doesn't
   persist to caller); register_layers is idempotent re-derive.
5. aop import path is `std.nogc_sync_mut.src.aop` (arch said reuse aop; correct module path).
6. arg_parser `main()` uses a hardcoded representative arg vector: `rt_get_args` is unresolved
   under the interpreter. Arg-parsing LOGIC is proven via `arg_parse_sample`. **Later waves /
   compiled-native path must inject real argv.**

**Blockers for later waves / verify:**
- argv injection for native entries needs a compiled-native path (interpreter lacks rt_get_args).
- Wave-2+ owns: log.spl `log_set_level`, log_level/web_login/vcs/help_info samples, all docs
  (glossary/_tldr/arch/design AC-14/15), spipe skill update (AC-16). samples_spec stays RED until then.
- The two interpreter limitations above will keep codec/di_authz specs partly RED regardless;
  verify against the probes for ground truth, not the it-block matcher reds.
