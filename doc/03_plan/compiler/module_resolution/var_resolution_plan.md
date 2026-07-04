# Plan: `var/` Variant Resolution Overlay

**Date:** 2026-06-29
**Domain:** compiler / module_resolution
**Lane:** `.spipe/var-resolution-overlay`
**Research:** `doc/01_research/local/var_resolution_rules.md`
**Status:** plan (ready for spec/impl phases)

## 1. Goal & non-goals

**Goal.** A resolver-only overlay (`var/`) that selects platform / hardware /
library / renderer implementations via SDN config + module resolution + DI
profile wiring. Source imports stable names; config picks the variant.

**Non-goals (hard constraints).**
- **No new grammar.** No `@var`, `@various`, `#[var]`, new keyword, or
  conditional-compilation syntax. `var` stays the mutable-variable keyword.
- **`var/` is resolver-only.** `use var.*` is forbidden (E-VAR005). `var` is not
  a public namespace.
- **No new tag surface.** Reuse SDN + `__init__.spl` manifest + DI profiles.

## 2. Design summary

### 2.1 Layout

```
src/                     # stable modules == implicit global default
  crypto/provider.spl
  fs/path.spl
var/
  __init__.spl           # SDN manifest, resolver-owned (group declarations)
  default/               # global fallback
    crypto/provider.spl
  platform/{default,mac,linux,windows,freebsd,baremetal}/...
  hw/{default,x86_64,arm64,riscv64,wasm32}/...     # subsumes variants/<simd_tier>/
  lib/crypto/{default,openssl,mbedtls}/crypto/provider.spl
  ui/renderer/{default,cpu,metal,vulkan,webgpu}/...
```
Dotted group names map to nested dirs: `lib.crypto` → `var/lib/crypto/<value>/`.

### 2.2 Manifest — `var/__init__.spl` (SDN, resolver-owned)

```sdn
var:
  version: 1
  default: default
  order: [platform, hw, lib.crypto, ui.renderer]
  groups:
    platform:   { values: [default, mac, linux, windows, freebsd, baremetal], detect: host.platform, select_default: auto }
    hw:         { values: [default, x86_64, arm64, riscv64, wasm32], detect: host.arch, select_default: auto }
    lib.crypto: { values: [default, openssl, mbedtls], select_default: default }
    ui.renderer:{ values: [default, cpu, metal, vulkan, webgpu], select_default: default }
  policy:
    unknown_group: error
    unknown_value: error
    duplicate_same_rank: error
    direct_var_import: error
    default_required: error
    src_is_default: true
    cache_includes_var_fingerprint: true
```
**Rule (RubyGems-style):** every group MUST contain `default`; every fallback
chain MUST end at `default`.

### 2.3 Project selection — `config/var.sdn`

```sdn
var:
  profile: dev
  profiles:
    dev:       { platform: auto, hw: auto, lib.crypto: default, ui.renderer: cpu }
    prod:      { platform: auto, hw: auto, lib.crypto: openssl, ui.renderer: auto }
    mac_metal: { platform: mac,  hw: auto, lib.crypto: openssl, ui.renderer: metal }
```
**Precedence:** CLI override → env override → `config/var.sdn` profile →
manifest `select_default` → host detection (for `auto`) → `default`.

CLI: `simple build --var platform=mac --var hw=arm64`,
`simple test --var-profile mac_metal`.
Env: `SIMPLE_VAR_PLATFORM`, `SIMPLE_VAR_HW`, `SIMPLE_VAR_LIB_CRYPTO`.

### 2.4 Candidate root order (Node-style: specific → default → src)

For `{platform: mac, hw: arm64, lib.crypto: openssl}` with the manifest `order`:
```
var/platform/mac  var/hw/arm64  var/lib/crypto/openssl   # all selected first
var/platform/default  var/hw/default  var/lib/crypto/default
var/default
src                                                       # global default
```
**All selected roots beat all default roots** (prevents a high-priority group's
default from hiding a low-priority group's selection). Selected-vs-selected ties
broken by `order`; same-rank collision → E-VAR004.

### 2.5 Resolver hook

Insert `try_var_roots(path, from_file)` **after** relative/local resolution and
**before** stdlib/source-root fallback — Rust resolution.rs:579, Simple
resolution.spl:67–68. Returned resolutions carry origin `"var"`.

## 3. Hardening decisions (from research §4)

- **H1 — Unify with existing SIMD variants.** `var/hw/<arch>/` generalizes the
  Rust-only `variants/<simd_tier>/` (stdlib_variant.rs). Migrate/bridge that tree
  under `var/hw/`; do not maintain two variant mechanisms.
- **H2 — Bootstrap-safe manifest read.** Parse `var/__init__.spl` with a minimal
  line-based SDN reader inside the resolver (mirror `di_config.spl`), never the
  full `sdn/parser.spl` (resolver precedes parser in bootstrap → cycle risk).
  E-VAR006 on malformed manifest.
- **H3 — DI by profile, not path.** `di.profile.var_profile` binds the active var
  profile; variant selection happens transparently when factory modules load.
  No service-level variant map. E-VAR008 if DI ever resolves a raw `var/...` path.
- **H4 — Parity is acceptance.** Land in **both** resolvers and **close the
  pre-existing Simple cache-key gap** (add tier/var fingerprint to
  resolution.spl:39 — currently `"segments;from_file"`, Rust already hashes
  `active_simd_tier_name()`). E-VAR007 guards the missing fingerprint.
- **H5 — Fail closed.** Unknown group/value, missing `default`, ambiguous rank,
  direct `var.*` import are errors. Tighten research §2.5 fail-open sites that
  `var/` supersedes (cfg_detect_os/arch "unknown" silent returns).

## 4. Phased implementation

| Phase | Deliverable | Key files |
|---|---|---|
| 1 ✅ | Research + requirements | `doc/01_research/local/var_resolution_rules.md` (done), `doc/02_requirements/feature/var_resolution_rules.md` |
| 2 | Architecture + design | `doc/04_architecture/compiler/module_resolution/var_resolution_rules.md`, `doc/05_design/.../var_resolution_rules.md` |
| 3 | Manifest model (both) | Rust `module_resolver/var_manifest.rs`, `var_resolution.rs`; Simple `99.loader/module_resolver/var_manifest.spl`, `var_resolution.spl`. Extend resolver state: `var_manifest`, `active_var`, `var_roots`, `var_fingerprint`. No parser change. |
| 4 | Resolver hook + cache | resolution.rs / resolution.spl: `try_var_roots()` at the seam; cache key `segments + from_file + var_fingerprint` (closes H4 gap). |
| 5 | Config + CLI | `config/var.sdn`; flags `--var key=value`, `--var-profile`; debug `simple var {list,check,roots,resolve}`. |
| 6 | DI wiring | `di_config.spl`: read `var_profile` per profile; bind active var profile before factory-module resolution. No service-decl change. |
| 7 | LSP + diagnostics | hover/go-to shows resolved var path + fallback; emit E-VAR001–008. |
| 8 | Tests | unit + system specs (§6). |

## 5. Diagnostics (fail-closed contract)

```
E-VAR001 unknown variant group
E-VAR002 unknown variant value
E-VAR003 selected variant requires missing default
E-VAR004 ambiguous provider at same rank
E-VAR005 direct var import is forbidden
E-VAR006 var/__init__.spl is invalid SDN
E-VAR007 resolver cache key missing variant fingerprint
E-VAR008 DI resolved unstable variant path directly
```
Example:
```
E-VAR005: direct var import is forbidden
  use var.platform.mac.fs.path
help: import the stable module path instead:
  use fs.path
```

## 6. Test matrix (Phase 8 acceptance)

Unit (`test/01_unit/compiler/module_resolver/`): `var_manifest_sdn_spec`,
`var_root_order_spec`, `var_default_required_spec`, `var_cache_fingerprint_spec`.
System (`test/03_system/compiler/module_import/`): `var_resolution_selected_spec`,
`..._default_spec`, `..._direct_import_forbidden_spec`, `..._di_spec`.

Required scenarios: selected beats default; any selected beats any default;
group order breaks selected-vs-selected; group/global/`src` defaults each work;
missing default fails (strict); unknown group/value fails; direct `var.*` fails;
DI stable module resolves to selected variant; **cache invalidates on var-profile
change** (Rust *and* Simple — closes the parity gap); Rust/Simple results match
for the focused matrix.

## 7. Guide & process doc updates (freshness gate, part of completion)

- `doc/07_guide/compiler/module_resolver.md` — add "Var Resolution Overlay"
  section after stdlib axes (root order, default rule).
- `doc/07_guide/compiler/var_resolution.md` — new operator/developer guide
  (declare groups, select profiles, add platform/library impls, default fallback,
  DI usage, `simple var check/resolve`, fixing diagnostics).
- SPipe process: add var-resolution-lane coverage requirements to
  `.claude/skills/spipe.md`, `.codex/skills/sp_dev/SKILL.md`,
  `.agents/skills/{impl,verify}/SKILL.md` (selected/default/ambiguity/direct-import
  + Rust↔Simple parity + cache-fingerprint must be proven before PASS).
- README feature bullet — **only after real impl lands.**

## 8. Related cleanup (separate, in-flight)

The `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/platform/` triplication
is **tier duplication, not a variant** — it does not belong in `var/`. Dedup it
to `src/lib/common/platform/` with tiers re-exporting (`export use
common.platform.X`). `config.spl` already moved (canonical written + 3 tier
shims; **verification pending** — was interrupted). Track separately; it
de-risks the resolver work by shrinking the platform surface.

## 9. Risks

- **Bootstrap cycle** if the manifest read pulls the SDN parser (mitigated by H2).
- **Resolver-cache correctness** is the highest-severity risk: a stale entry
  returns the wrong variant for the same process across profiles. H4 + the
  fingerprint test are non-negotiable.
- **Parity drift** already exists; the lane must reduce it, not add to it.
- **Migration of existing `variants/<simd_tier>/`** must not break SIMD builds —
  bridge before removing.
