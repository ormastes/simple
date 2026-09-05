# Research: `var/` Variant Resolution Overlay

**Date:** 2026-06-29
**Domain:** compiler / module_resolution
**Lane:** `.spipe/var-resolution-overlay`
**Status:** research (grounded against repo)

## 1. Problem

Platform/environment-specific logic is selected today by a scattered mix of
mechanisms with no single configurable interface, and several paths fail *open*
(silently default) instead of *closed* (error). We want one resolver-only
overlay that selects platform / hardware / library / renderer implementations
**without adding any new language grammar** (no `@var`, no `#[var]`, no new
keyword, no conditional-compilation syntax). Selection lives in SDN config +
module resolution + DI profile wiring.

Key grammar constraint: `var` is **already a reserved keyword** (`KwVar`,
`src/compiler/10.frontend/lexer_types.spl:25`). Therefore `var/` must be a
**filesystem/resolver root only**, invisible to source imports. `use var.*`
must be rejected, not supported.

## 2. Current state (grounded)

### 2.1 Module resolver (Rust seed + self-hosted Simple)

| | Rust seed | Self-hosted Simple |
|---|---|---|
| Dir | `src/compiler_rust/compiler/src/module_resolver/` | `src/compiler/99.loader/module_resolver/` |
| Files | `mod.rs`, `resolution.rs`, `manifest.rs`, `types.rs` | `resolution.spl`, `types.spl`, `manifest.spl`, `__init__.spl` |
| Main fn | `ModuleResolver::resolve()` resolution.rs:464 | `resolve(path, from_file)` resolution.spl:20 |
| Insertion seam | resolution.rs:579 (after relative, before stdlib) | resolution.spl:67–68 (after relative, before stdlib) |
| Cache key | `hash(segments + base_dir + active_simd_tier_name())` path_resolution.rs:59–65 | `"segments;from_file"` resolution.spl:39 / types.spl:301 |

Resolution order (both, per `doc/07_guide/compiler/module_resolver.md:5–14`):
relative → `crate.*` → stdlib (`std.*`/`lib.*` family fallback) → `compiler.*`
(numbered-dir strip) → numbered dir → source-root fallback.

`__init__.spl` is already a directory manifest (Rust resolution.rs:166, Simple
resolution.spl:230) used for wildcard re-exports, directory attributes
(`#[no_gc]`), and the common-uses prelude. **This is the precedent for parsing
`var/__init__.spl` as a resolver-owned manifest.**

### 2.2 PARITY GAP (pre-existing, load-bearing)

Rust already implements a **hardware variant root** mechanism:
`variants/<simd_tier>/src` is prepended at stdlib resolution
(`stdlib_variant.rs:30–52`, called from resolution.rs:596–624), and the SIMD
tier is folded into the **cache key**. The **Simple resolver implements neither**
— no `variants/<tier>/` search, and its cache key omits the tier entirely. The
guide mandates Rust/Simple parity (module_resolver.md:137–138), but the code has
drifted. A `var/` overlay must **generalize and unify** this existing axis (as
`var/hw/<arch>/`), not add a third parallel mechanism, and must close the Simple
cache-key gap.

### 2.3 DI config

- SDN config + loader: `src/compiler/00.common/di_config.spl`
  (`parse_di_config`, `di_setup_from_config_with_profile` line 228). Structs:
  `DiServiceConfig{name, module_path, factory_name, lazy_mode, is_singleton}`,
  `DiProfileConfig{name, lazy_default}`, `DiConfig{default_profile, profiles, services}`.
- **DI does NOT route through the module resolver.** `di.spl:157 resolve()` maps
  service names to factory bindings in a `Dict`, pre-registered per profile.
  Implication: variant selection happens transparently when a factory's *module*
  is loaded (its `use` statements hit the resolver). DI needs no service-level
  variant map — it only needs the active **var profile bound to the di profile**.
- DI uses a **manual line-based SDN read** to avoid pulling the full SDN parser
  into the bootstrap chain. The resolver is *earlier* in bootstrap than DI, so
  `var/__init__.spl` parsing should mirror this (minimal line reader), not import
  `src/lib/common/sdn/parser.spl:8 parse()`, to avoid a resolver→parser cycle.

### 2.4 Tag systems & keyword (confirms "no new grammar" is free)

- `@decorator`: `src/compiler/10.frontend/parser_extensions.spl:38 parse_attributes()`.
- `#[...]`: `HashLBracket` token lexer_types.spl:131; parsed in `_Attributes/`.
- The two systems overlap; no unified cleanup doc exists. The `var/` design sides
  with "add no surface form at all," sidestepping the overlap question entirely.

### 2.5 Existing platform-variation fail-OPEN inventory (hardening targets)

| Site | Behavior on unknown |
|---|---|
| `cfg_platform.spl:144 cfg_detect_os()` | returns `"unknown"` silently (FAIL-OPEN) |
| `cfg_platform.spl:167 cfg_detect_arch()` | returns `"unknown"` silently (FAIL-OPEN) |
| `platform_attr_parser.spl` validation | sets `is_valid=false`, caller may ignore (FAIL-OPEN) |
| `smf_enums.spl:35 Platform.from_u8()` | defaults to `Platform.Any` (SILENT) |
| `linker/platform_defaults.spl:68–148` | returns empty arrays for unknown OS/arch (FAIL-OPEN downstream) |
| `config.spl host_config()` | 2-way `windows ? "\r\n" : "\n"` (implicit default) |
| Tier `platform/` dir | `config/convert/newline/wire/text_io/mod` triplicated across `nogc_sync_mut`/`nogc_async_mut`/`gc_async_mut`; only the `use <tier>.` prefix differs (`config.spl` byte-identical). Pure dup, not a variant. |

`HardeningPolicy` (platform_defaults.spl:53–61) is the one FAIL-SAFE example
(unknown preset → fully hardened) — the model to copy.

## 3. Prior art

- **RubyGems / default gems** — "always-default" rule: a default implementation
  is always require-able; platform-specific gems are enhancements layered on top.
  → every `var/` group must contain `default`; selected variants enhance, never
  replace, the default path.
- **Node conditional exports** — `"default"` always matches and must come *last*;
  conditions ordered most-specific → least-specific. → resolver order: selected
  variant roots first, then group defaults, then global `var/default`, then `src/`.
- **Cargo `target.'cfg(...)'.dependencies`** — platform selection is *config*,
  not import grammar. → take the lesson (config selects impl) while rejecting the
  cfg-grammar expansion.

## 4. Findings → hardening decisions (carried into the plan)

- **H1 — Unify, don't fork.** `var/hw/<arch>/` subsumes the existing Rust
  `variants/<simd_tier>/`. Close the Simple cache-key gap in the same lane.
- **H2 — Bootstrap-safe manifest.** Parse `var/__init__.spl` with a minimal
  line-based SDN reader in the resolver (mirror `di_config.spl`), not the full
  parser.
- **H3 — DI by profile, not by path.** `di.profile.var_profile` selects the
  active var profile; the resolver does the rest when factory modules load. No
  service-level variant map.
- **H4 — Parity is acceptance.** Land in *both* resolvers; the lane closes the
  pre-existing SIMD drift, not just adds var/.
- **H5 — Fail closed.** Unknown group/value, missing required `default`,
  ambiguous same-rank provider, and direct `var.*` import are all errors
  (E-VAR001–008). Tighten the §2.5 fail-open sites that `var/` supersedes.

## 4b. BLOCKER — `var/` root name collision (discovered on disk)

The proposed overlay root `var/` **already exists and is in active use** as
FHS-style runtime/state data, and is git-tracked:

```
var/lib/simple_portal/run-1.json
var/lib/web_stack_sample/sample.sdn
var/lib/web_stack_sample/sample.sdn.wal
```

`var/lib/` is the Unix `/var/lib` convention (mutable program state). Repurposing
`var/` as a compiler variant overlay would collide directly — e.g. `var/lib/` is
both "runtime state" and (per spec) "library variant group". Separately, the Rust
resolver already references a `variants/<simd_tier>/` root mechanism
(`stdlib_variant.rs`), though no `variants/` directory exists on disk yet.

**Decision required before Phase 3** (changes every implementation path):
- **Option A (recommended): name the overlay `variants/`** — the name the Rust
  resolver already uses for the SIMD axis. Reuses an existing concept (satisfies
  H1 unification), no collision with `var/lib` runtime data, and keeps the keyword
  `var` strictly a language token. Cost: spec says `var/` throughout → rename.
- **Option B: keep `var/`, relocate the runtime-state data** (e.g. to
  `build/var/` or `.state/`). Cost: touches `simple_portal`/`web_stack_sample`
  consumers; risk to live data.
- **Option C: nest the overlay under `var/overlay/`** or similar. Cost: uglier,
  still conflates two meanings of `var/`.

## 5. Open questions

- Does the existing SIMD `variants/` tree get migrated under `var/hw/` now, or
  bridged by an alias during transition?
- Strict mode (`default_required: error`, `src_is_default: false`) for core libs
  vs transition mode (`warn` / `src_is_default: true`) repo-wide — per-group?
- Cache fingerprint scope: global var-profile hash vs per-group (matters for
  incremental rebuild granularity).

See plan: `doc/03_plan/compiler/module_resolution/var_resolution_plan.md`.
