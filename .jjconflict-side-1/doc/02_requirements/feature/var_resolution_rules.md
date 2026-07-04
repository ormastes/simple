# Spec: `var/` Variant Resolution Overlay (canonical request)

**Date:** 2026-06-29
**Domain:** compiler / module_resolution
**Lane:** `.spipe/var-resolution-overlay`
**Status:** requirements / canonical spec (verbatim from request, annotated)
**Companion:** research `doc/01_research/local/var_resolution_rules.md`,
plan `doc/03_plan/compiler/module_resolution/var_resolution_plan.md`

> ⚠️ **Open blocker (see research §Findings):** the on-disk root `var/` is
> already used for FHS-style runtime state data (`var/lib/simple_portal/`,
> `var/lib/web_stack_sample/`, git-tracked). The overlay root name must be
> resolved (reuse `variants/` — already referenced by the Rust resolver — or
> another name) before Phase 3 implementation. Everything below uses `var/` as a
> placeholder for the chosen overlay root.

## 1. Design goals

`var/` is a module-resolution overlay. Normal code imports stable names:

```simple
use crypto.provider
use fs.path
use app.gui.surface
```

Normal code must **not** import variant paths (rejected — E-VAR005):

```simple
use var.platform.mac.fs.path          # invalid
use var.lib.crypto.openssl.crypto.provider  # invalid
```

The resolver may search `var/` internally, but `var` is not a public module
namespace. `var` is already a keyword (`KwVar`), so it can never be importable.

No new grammar: no `@var`, `@various`, `#[var]`, new keywords, or conditional
syntax. Selection = SDN config + module resolution + DI profile wiring.

## 2. Canonical layout

```
src/
  crypto/provider.spl
  fs/path.spl
  app/gui/surface.spl
var/
  __init__.spl              # SDN manifest, resolver-owned
  default/
    crypto/provider.spl
    fs/path.spl
  platform/{default,mac,linux,windows}/...
  hw/{default,x86_64,arm64}/atomic.spl
  lib/crypto/{default,openssl,mbedtls}/crypto/provider.spl
```
Dotted group names map to nested dirs: `lib.crypto` → `var/lib/crypto/<value>/`,
`ui.renderer` → `var/ui/renderer/<value>/`.

## 3. `var/__init__.spl` is SDN, only in `var/`

Only `var/__init__.spl` is parsed as a variant SDN manifest by the resolver. No
change to general `.spl` parsing. `__init__.spl` is already a resolver manifest
file, so this is a resolver-manifest rule, not expression grammar.

```sdn
var:
  version: 1
  default: default
  order: [platform, hw, lib.crypto, ui.renderer]
  groups:
    platform:    { values: [default, mac, linux, windows, freebsd, baremetal], detect: host.platform, select_default: auto }
    hw:          { values: [default, x86_64, arm64, riscv64, wasm32], detect: host.arch, select_default: auto }
    lib.crypto:  { values: [default, openssl, mbedtls], select_default: default }
    ui.renderer: { values: [default, cpu, metal, vulkan, webgpu], select_default: default }
  policy:
    unknown_group: error
    unknown_value: error
    duplicate_same_rank: error
    direct_var_import: error
    default_required: error
    src_is_default: true
    cache_includes_var_fingerprint: true
```
**Required rule (Ruby-like):** every group must contain `default`; every fallback
chain must end in `default`.

## 4. Project config selection — `config/var.sdn`

```sdn
var:
  profile: dev
  profiles:
    dev:       { platform: auto, hw: auto, lib.crypto: default, ui.renderer: cpu }
    prod:      { platform: auto, hw: auto, lib.crypto: openssl, ui.renderer: auto }
    mac_metal: { platform: mac,  hw: auto, lib.crypto: openssl, ui.renderer: metal }
```
**Selection precedence:** CLI override → environment override → `config/var.sdn`
selected profile → manifest `select_default` → host detection for `auto` →
`default`.

CLI: `simple build --var platform=mac --var hw=arm64 --var lib.crypto=openssl`,
`simple test --var-profile mac_metal`.
Env: `SIMPLE_VAR_PLATFORM`, `SIMPLE_VAR_HW`, `SIMPLE_VAR_LIB_CRYPTO`.

## 5. Candidate root order

For `{platform: mac, hw: arm64, lib.crypto: openssl}` with `order:
[platform, hw, lib.crypto]`:
```
var/platform/mac  var/hw/arm64  var/lib/crypto/openssl   # selected, in group order
var/platform/default  var/hw/default  var/lib/crypto/default   # group defaults
var/default                                              # global default
src                                                      # source fallback
```
**All selected roots beat all default roots.** Selected-vs-selected ties broken
by group `order` (platform before hw → platform/mac wins). Same-rank collision →
E-VAR004 `ambiguous var provider for fs.path`.

## 6. Module resolution hook

Preserve existing order. Insert `var` after local relative resolution fails and
before stdlib/source-root fallback.

```
resolve(use_path, from_file):
  1. explicit relative  -> existing resolver only
  2. crate.*            -> existing resolver only
  3. local/relative base resolution
  4. active var candidate roots      <-- NEW
  5. existing stdlib/compiler/source-root strategies
```
```
fn resolve(path, from_file):
    if path.is_empty: error
    if path.starts_with("crate") or path.is_explicit_relative:
        return resolve_existing(path, from_file)
    match resolve_relative_existing(path, from_file):
        Ok(r): return r
        Err(_): pass
    for root in active_var_roots:
        match resolve_from_base(root, path.segments, path):
            Ok(r): return r.with_origin("var")
            Err(_): continue
    return resolve_existing_fallbacks(path, from_file)
```
**Cache key must include the active variant fingerprint:** old `segments +
from_file` → new `segments + from_file + var_profile_hash`. Without it,
`--var-profile mac` and `--var-profile linux` reuse the wrong resolved path in
the same process. (Note: the self-hosted Simple cache key today lacks even the
SIMD tier — see research §2.2.)

## 7. Default rule

For every non-default variant file `var/<group>/<value>/<module>.spl`, at least
one fallback must exist: `var/<group>/default/<module>.spl`,
`var/default/<module>.spl`, or `src/<module>.spl` (only when `src_is_default:
true`).

Strict mode for core libs: `default_required: error`, `src_is_default: false`.
Transition mode: `default_required: warn`, `src_is_default: true`.

## 8. DI integration

Keep `config/di.sdn` stable; no variant-specific service syntax.
```sdn
di:
  services:
    crypto: { module: crypto.provider, factory: create, lazy: auto, singleton: true }
  default_profile: prod
  profiles:
    prod: { lazy: true,  var_profile: prod }
    test: { lazy: false, var_profile: test }
```
Resolution: `crypto.provider` → `var/lib/crypto/openssl/crypto/provider.spl`
(prod), falling back through `var/lib/crypto/default` → `var/default` → `src`.
**No service-level variant map needed.** (Note: DI does not call the resolver
directly — selection happens when the factory's module loads; research §2.3.)

## 9. Diagnostics

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
```
E-VAR005: direct var import is forbidden
  use var.platform.mac.fs.path
help: import the stable module path instead:
  use fs.path
```

## 10. Phased refactoring plan (summary; detail in plan doc)

1. Research + requirements docs (this doc + research).
2. Architecture + design docs (`doc/04_architecture/...`, `doc/05_design/...`).
3. Manifest model — Rust `var_manifest.rs`/`var_resolution.rs`, Simple
   `var_manifest.spl`/`var_resolution.spl`; extend resolver state. No parser change.
4. Resolver hook `try_var_roots()` + cache key fingerprint (both resolvers).
5. `config/var.sdn` + CLI `--var key=value` / `--var-profile` + `simple var
   {list,check,roots,resolve}`.
6. DI wiring (`di.profile.var_profile` → active var profile).
7. LSP hover/go-to var awareness + diagnostics E-VAR001–008.
8. Tests — unit (`test/01_unit/compiler/module_resolver/var_*`) + system
   (`test/03_system/compiler/module_import/var_resolution_*`).

## 11. Guide & process doc updates (completion gate)

- `doc/07_guide/compiler/module_resolver.md` — add "Var Resolution Overlay".
- `doc/07_guide/compiler/var_resolution.md` — new operator/developer guide.
- SPipe process: var-resolution-lane coverage in `.claude/skills/spipe.md`,
  `.codex/skills/sp_dev/SKILL.md`, `.agents/skills/{impl,verify}/SKILL.md`.
- README feature bullet — only after real impl lands.

## 12. Final recommendation (verbatim)

Implement var as **filesystem root + SDN manifest + resolver overlay + DI profile
input**, not **new grammar + new tags + direct variant imports**. The clean rule:
source imports stable names; config selects variants; resolver searches var roots;
default always exists; DI uses stable module paths; SPipe proves
selected/default/error behavior.
