# SFM (.sfm) — Verification Report

Interpreter binary used: `bin/release/aarch64-apple-darwin-macho/simple`
(`bin/simple` is a Linux binary on this macOS host).

## AC verification matrix

| AC | Status | Evidence |
|----|--------|----------|
| AC-1 container round-trip | PASS | `sfm_roundtrip_probe.spl` → `SFM-ROUNDTRIP: PASS`; `sfm_codec_spec` 8/8 |
| AC-2 manifest layers | PASS | `sfm_codec_spec` AC-2 blocks (role/kind/entry round-trip) |
| AC-3 DI resolve-by-role | PASS | `sfm_di_authz_spec` AC-3 (data-driven `register_layers`/`resolve_layer`) |
| AC-4 AOP allow/deny | PASS | `sfm_di_authz_spec` AC-4 (allow ordinary, deny+allow privileged) |
| AC-5 special security level | PASS | `sfm_di_authz_spec` AC-5 (Trusted gates; Ordinary ungated) |
| AC-6 profiles native/loader/script/web/mobile | PASS* | `sfm_loader_profiles_spec` 6/6; *mobile is a thin load-and-report shim (per scope) |
| AC-7 arg-parser native sample | PASS* | `sfm_samples_spec` + arg_parser probe; *native argv hardcoded under interpreter (no `rt_get_args`), parse logic proven |
| AC-8 log-level changer | PASS* | log_level probe OK; *observability via in-call-flow level read (interpreter module-global staleness) |
| AC-9 web login | PASS | web_login probe: valid→authenticated, invalid→denied via authz gate |
| AC-10 VCS support | PASS | vcs probe: status (branch/clean) + commit (hash) |
| AC-11 Help/Info menu | PASS | help_info probe surfaces Module + Version + SFM marker |
| AC-12 VERSION.md build | PASS | `VERSION.md` (0.1.0) created; `read_version_md` reads it; help_info shows 0.1.0 |
| AC-13 reusable infra | PASS | `reuse_consumer` + sample apps consume public `std.sfm` API |
| AC-14 glossary+tldr | PASS | `doc/simple_feature_module_glossary.md`(+tldr), linked from `doc/glossary.md`, SDN diagram |
| AC-15 arch+design docs | PASS | `doc/04_architecture/` + `doc/05_design/` (+tldrs), each ≥1 SDN diagram, ≤30 lines prose |
| AC-16 SPipe skill | PASS | `.claude/skills/spipe.md` Feature-Module-Packaging (.sfm) section |

## Spec results (interpreter)
- `sfm_codec_spec`: 8/8 · `sfm_di_authz_spec`: 10/10 · `sfm_loader_profiles_spec`: 6/6 · `sfm_samples_spec`: 11/11 · AC-1 probe: PASS

## Refactor / quality
- Specs converted `to_be_true`/`to_be_false` → `assert_true`/`assert_false` (the `testing.md`-preferred form) to dodge the interpreter matcher bug; codec re-encode logic extracted to a top-level `reencode_matches` helper (tuple-arm var-scope bug). Both bugs filed under `doc/08_tracking/bug/` (2026-06-04).
- Numbered-artifact guard: OK. No SFM core file >800 lines (552 total / 7 files).

## Honest caveats (in scope)
- 3 ACs marked PASS* run under documented interpreter workarounds (argv injection, log staleness) — proven via callable fns/probes; full native argv needs a compiled build.
- Mobile profile is a load-and-report shim; app-store packaging is out of scope per the state file.

## VCS
All work committed on `main` ancestry across several commits (core lib, samples, docs, spec green-fixes, bug docs). Commit IDs were rebased repeatedly by concurrent agents; content verified intact on disk and in history.
