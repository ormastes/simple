# CPU-Tier Multi-Build: one baseline binary + one dylib per tier (design, 2026-10-27)

**Directive.** When CPU-tier code applies, a build emits **all tiers by default** (baseline built in,
one shared library per extra tier); `--cpu-tier <t>` builds/links only `<t>`. The binary probes
cpuid/hwcap at startup, loads the best fully-supported tier dylib, and falls back to built-in
baseline. Scope: **SIMD/CPU tiers only** — compiler-backend dylibs are a separate lane
(`backend_dynamic_plugin_build_groups.md`, wt-backend-dylib; coordinate the build entry point, § 6).

## 1. Tier set, canonical tuple, LLVM mapping, cache key

A **tier** is `TierId(arch, base_level, features: sorted [text])`, written `base[+feat...]`.
Base levels are LLVM `-target-cpu`/`-march` names; features are LLVM `-target-feature` names.

| arch | default (named) levels, baseline first | example feature tiers |
|---|---|---|
| x86_64 | `x86-64` (alias `x86-64-v1`), `x86-64-v2`, `x86-64-v3`, `x86-64-v4` | `x86-64-v2+avx2`, `x86-64-v4+avx512vnni` |
| aarch64 | `armv8-a`, `armv8.2-a`, `armv9-a`; default tier `armv9-a+sve` | `armv8.2-a+dotprod`, `armv9-a+sve2` |
| riscv64 | `rv64gc`, `rv64gcv` | `rv64gcv+zvbb` |

**Canonicalization** (`tier_canonicalize`): resolve aliases; drop every feature in
`implied_features[base]`; sort + dedupe. Equal canonical tuples ⇒ identical cache key and artifact
name (`libsimple_tier_<arch>_<base>[+f...].{so,dll,dylib}`). **Admission partial order** (used by
the dispatcher): same arch ∧ `rank(base) <= rank(host_level)` ∧ every feature ∈ host features.

Config `config/build/cpu_tiers.sdn` (schema pinned here; the lib-versioning lane reads it):
```
cpu_tiers:
  - arch: x86_64
    levels: [x86-64, x86-64-v2, x86-64-v3, x86-64-v4]        # ordered, baseline first
    aliases: {x86-64-v1: x86-64}
    implied_features: {x86-64-v2: [sse3, ssse3, sse4.1, sse4.2, popcnt], x86-64-v3: [avx, avx2, bmi, bmi2, fma, f16c, movbe], x86-64-v4: [avx512f, avx512bw, avx512cd, avx512dq, avx512vl]}
    default_tiers: [x86-64, x86-64-v2, x86-64-v3, x86-64-v4]
    feature_tiers: []                                          # user-added: [{base: x86-64-v4, features: [avx512vnni]}]
  - arch: aarch64 ... levels: [armv8-a, armv8.2-a, armv9-a]; default_tiers: [armv8-a, armv8.2-a, armv9-a+sve]
  - arch: riscv64 ... levels: [rv64gc, rv64gcv]
```
`--cpu-tier x86-64-v3+avx512vnni` (CLI) and `SIMPLE_CPU_TIER` go through the same canonicalizer.

**Existing code reused.**
- Rust seed object key: `object_cache_key` at `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1922-1943`
  already hashes `SIMPLE_NATIVE_CPU` (`:1938`) and `active_simd_tier_name()` (`:1939`, from
  `stdlib_variant.rs:12`). Gap: those names are the legacy `SimdTier` strings (`x86_64_avx2`,
  `simd/src/detection.rs:12-40`), not LLVM names. Fix: hash the canonical tuple text instead.
- Pure-Simple scope key: `native_build_cache_scope_key(backend, target_cpu, target_features, ...)`
  at `src/compiler/80.driver/driver_build/incremental.spl:645-674` already frames `cpu=` and
  `features=` — feed it the canonical tuple (`cpu=<base>`, `features=<sorted>`); no new field.
- Level names already exist: `TargetCpu::X86_64V1..V4` (`codegen/common_backend.rs:1228-1237`),
  `--cpu default|native|x86-64-v1..v4` (`src/app/cli/native_build_main.spl:277`, parsed in
  `src/app/cli/environment_variant_policy_sources_v1.spl:69`), LLVM cpu names in
  `codegen/llvm/backend_core.rs:150-160`. **Note:** `default_x86_64_cpu_name` defaults to
  `x86-64-v3` (`:151`); the baseline unit must force `x86-64`.
- Feature ids: `ENV_FEATURE_X86_64_BASELINE_V1..V4`, `AARCH64_NEON/SVE/SVE2`, `RISCV64_RVV`
  (`src/lib/nogc_sync_mut/composition/environment_variants/feature_registry_v1.spl:23-46`);
  `target_codegen_features_subset_v1` (`target_codegen_profile_v1.spl:195`) is the subset test.
- **HIR stays target-neutral; MIR/backend picks the tier**: `mir_cfg_eval_for_target(cond, target,
  features)` (`src/compiler/50.mir/mir_cfg_select.spl:127`) already evaluates
  `target_feature = "..."` atoms (`:76`) against a `features: [text]` list. The tier's expanded
  feature set (base-implied ∪ explicit) is that list. `MirTargetContext`
  (`src/compiler/00.common/mir_target_context.spl:3`) gains `cpu_tier: text = ""`.

## 2. Tier-specific vs tier-neutral classification

A MIR unit is **tier-specific** iff any of: `@cfg(target_feature=...)` arm selected via
`mir_cfg_select_arm` (`mir_cfg_select.spl:137`); `@simd` / `@must(simd)` decl attrs
(`src/compiler/00.common/_Attributes/decl_attrs.spl:234,681-685`) with the auto-vectorizer
provider active (`60.mir_opt/mir_opt/auto_vectorize_provider.spl`, `simd_recipe_infra.spl`);
std SIMD modules (`src/lib/gc_sync_mut/simd/{fixed,scalable,mask,vector}.spl`,
`src/lib/common/simd_scan.spl`, `crypto/sha256_simd.spl`); or runtime C kernels under
`src/runtime/providers/vector/` (`bitmap_avx512.c`, `bitmap_neon.c`, `bitmap_sve.c`,
`bitmap_rvv.c`, `http_*.c`). Everything else is **tier-neutral** and is lowered once at baseline.
The classifier is a pure function `tier_unit_kind(module) -> TierUnitKind {Neutral, Tiered}` and is
recorded in the per-module witness so cache hits are per-kind.

## 3. Multi-compile

Neutral modules: compiled once (`cpu=x86-64, features=[]`). Tiered modules: one object per tier in
`default_tiers ∪ feature_tiers`, scheduled as independent jobs over the existing shared-queue
worker fan-out (`native_build_main.spl:867,1180`), each under its own scope-key directory
(§ 1), so a re-run with an unchanged tier is a 100% cache hit. `--cpu-tier t` restricts the set to
`{t}`; `--cpu-tier none` = baseline only (what bootstrap uses).

**Per-tier stdlib archive interface (sibling lane).** The static-stdlib lane builds one archive per
`(target, tier)`. Contract: tier-**neutral** std objects go only into the baseline archive;
tier-**specific** std objects (§ 2 list) go into the per-tier archive, keyed by the **same canonical
tuple text** as § 1 (never the legacy `x86_64_avx2` spelling). The tier dylib links the per-tier std
archive plus the C kernels; the base binary links the baseline archive.

## 4. Multi-link

Default output = `simple` (baseline, static) + `tiers/libsimple_tier_<tuple>.{so,dll,dylib}` per
tier. Shared emission reuses `--emit-shared` (`native_build_main.spl:286`;
`src/app/build/targets/target_executor.spl:106-121`, `kind: shared`). Linker: clang + lld only
(Windows: llvm-mingw `x86_64-pc-windows-gnu`, `.dll` via `ld.lld`; Mach-O via `ld64.lld`). Where a
dylib is impossible (SimpleOS freestanding, `-static-pie` bare targets, wasm): emit **per-tier
binaries** `simple.<tuple>` instead, same selection rule applied by the installer/launcher.
`--cpu-tier t` links exactly one artifact and embeds `t` as the built-in level.

## 5. Runtime dispatch

Reuse the existing probe: `probe_level()` in `src/runtime/providers/vector/vector_level_dispatch.c:45-99`
(CPUID leaves 1/7/0x80000001 + XGETBV `:48-60`; aarch64 `HWCAP_ASIMD/SVE/SVE2` via getauxval `:75-79`;
riscv hwcap `'V'` + `prctl(70)` `:85-93`; `SIMPLE_VECTOR_MAX_LEVEL` cap `:108`). Today it forwards
to statically linked `simple_bitmap_kernel_lN` (`DISPATCH` macro `:146-152`). Change: extend the
probe to return a **feature bitmap** (not only a level), then `simple_tier_select(candidates)`
picks the highest-ranked tier whose base ≤ host level and whose features ⊆ host set; `dlopen`/
`LoadLibraryW` the matching dylib (Windows: `GetProcAddress`), else keep built-in baseline
(`vector_level_portable.c`). Loader: a lean sibling of the backend-plugin lease
(`src/compiler/70.backend/backend_plugin/dynamic_loader.spl:134` `load_dynamic_backend_plugin_lease`;
ABI header `backend_plugin/abi/simple_backend_plugin_v1.h:9,37`) — same `abi_version/struct_size`
descriptor prefix, tier tuple + feature set in the descriptor, mismatch ⇒ refuse and fall back.
C is only the probe/dlopen boundary; the selection logic is pure Simple
(`src/lib/common/cpu_tier/{tier_id,tier_select}.spl`) with the C `simple_tier_select` as its
dual-run twin (`scripts/check/check-dual-run-shadow.shs`). No `Any`, no inheritance.

## 6. Build-group integration

Entry point is the root `targets.sdn` named-target registry (`kind: binary|shared`,
`targets.sdn:6-16`), read by `src/app/build/targets/build_targets.spl:291 load_targets_file` and
`targets_cli.spl:72,129`. Add one `include:` directive to `build_targets.spl` (whichever lane —
this or backend-dylib — lands first owns it; the other rebases) and sub-configs under
`config/build/`: ours is `cpu_tiers.sdn` (§ 1) plus sub-script `scripts/build/build-cpu-tiers.shs`
that only enumerates tiers and invokes `simple build --target //tiers:<tuple>` — **no second
build system**. Tier dylibs form their own group `//tiers:*`; the default group stays host-only.
Bootstrap (`scripts/bootstrap/bootstrap-from-scratch.sh`) builds **host + baseline only**
(`--cpu-tier none`); tier dylibs are a post-bootstrap group.

## 7. Specs and evidence

All specs below are modern SSpec, **manual-first**: user-voice docstrings, outcome-named `it`
blocks, `step(...)`, `@manual_section`, `@req` — per `doc/07_guide/infra/sspec_antipatterns.md`
(no test-speak names, no assert-only bodies, no fake narrative). Evidence lanes:
(a) **tier-mismatch refusal** — a `x86-64-v4` dylib offered to a v3 host is refused with a named
reason; (b) **fallback path** — no dylib / corrupt descriptor ⇒ baseline runs, exit 0, receipt says
`tier=x86-64 source=builtin`; (c) **dual-run equality** — same inputs through every admitted tier
and baseline give byte-identical output (extends `check-vector-provider-levels.shs` parity lane and
`check-vector-bitmap-x86-avx512.shs`); (d) cache-key equality for `x86-64-v3+avx2` vs `x86-64-v3`.

### 7a. Rules added 2026-10-27 (user directives)

- **Build vs run.** Every tier must COMPILE and LINK on any host, even one whose CPU lacks the tier
  (e.g. no AVX-512 on the Broadwell dev host). Only RUN rows depend on the CPU: when cpuid/hwcap
  reports the feature missing, the row is reported *blocked* with the reason via `planned(...)`,
  never a build failure and never a silent `skip()`. Evidence on such hosts is static:
  `llvm-objdump -d` shows tier instructions (zmm/EVEX for x86-64-v4) and the IR/object carries the
  `target-cpu` attribute. The dispatcher test must prove that on the host it selects <= the host
  tier (<= v3 on Broadwell) and falls back cleanly to the baseline.
- **Five hosts.** The probe and tier builds cover Windows, Linux, macOS, FreeBSD and SimpleOS:
  cpuid/xgetbv on x86, `getauxval` (Linux), `elf_aux_info` (FreeBSD), `sysctlbyname` (macOS) and
  the SimpleOS kernel cpuid path. Each host has a modern SSpec row; an unreachable host stays a
  visible blocked row.
- **Static first, dylib second.** Per-tier static archives that link into per-tier binaries land
  first (PR5a). The tier dylib and loader (PR7) follow.
- **Default CPU.** The base x86_64 build is always `x86-64` (v1). There is no host-CPUID widening;
  v2-v4 come only from tier artifacts (landed in PR2).
- **`--cpu` flag bug.** `native-build --cpu=<lvl>` is silently ignored, and `--cpu <lvl>` fails
  admission (BUG-XC-CPU-FLAG-IGNORED, `doc/08_tracking/bug/bug_xc_cpu_flag_ignored_2026-10-27.md`).
  PR4 fixes it alongside `--cpu-tier`; acceptance is `x86_64_v4_cross_spec.spl`.

## 8. PR breakdown (small, Haiku-sized)

1. **Tier model + canonicalizer** — `src/lib/common/cpu_tier/tier_id.spl` (parse, alias, implied
   drop, sort, text form), `config/build/cpu_tiers.sdn`. Spec: `test/01_unit/lib/common/cpu_tier/tier_id_spec.spl`.
2. **Cache key carries the tuple** — `incremental.spl:645` call sites pass canonical tuple;
   `native_project/mod.rs:1938-1939` hash tuple text; `MirTargetContext.cpu_tier`. Spec:
   `test/01_unit/compiler/driver/cache_scope_cpu_tier_spec.spl`.
3. **Classifier** — `src/compiler/60.mir_opt/mir_opt/tier_unit_kind.spl` (uses `mir_cfg_select`,
   `decl_attrs`); witness field. Spec: `test/01_unit/compiler/mir_opt/tier_unit_kind_spec.spl`.
4. **Multi-compile schedule + `--cpu-tier`** — `native_build_main.spl` flag, `environment_variant_policy_sources_v1.spl`,
   per-tier job expansion. Spec: `test/02_integration/build/cpu_tier_multicompile_spec.spl`.
5. **Multi-link + targets group** (split: **5a** per-tier static archives + per-tier binaries, lands before PR7; **5b** `include: config/build/cpu_tiers.sdn` + `group cpu_tiers` default false on #5064 syntax) — `target_executor.spl` tier outputs, `build_targets.spl`
   `include:`, `//tiers:*`, `scripts/build/build-cpu-tiers.shs`. Spec: `test/02_integration/build/cpu_tier_targets_group_spec.spl`.
6. **Runtime probe → feature bitmap + selector twin** — `vector_level_dispatch.c` (bitmap probe,
   `simple_tier_select`), `src/lib/common/cpu_tier/tier_select.spl` twin, dual-run check hook.
   Spec: `test/01_unit/lib/common/cpu_tier/tier_select_spec.spl`.
7. **Dylib loader + fallback** — `src/runtime/providers/vector/tier_loader.c` (dlopen/LoadLibraryW
   boundary), `src/lib/nogc_sync_mut/cpu_tier/tier_loader.spl`, descriptor with `abi_version`.
   Spec: `test/02_integration/runtime/cpu_tier_fallback_spec.spl` (covers refusal + fallback).
8. **Evidence + bootstrap wiring** — `scripts/check/check-cpu-tier-dual-run.shs`, bootstrap
   `--cpu-tier none`, per-tier std archive handoff doc line. Spec:
   `test/03_system/build/cpu_tier_dual_run_equality_spec.spl`.
