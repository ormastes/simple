# Feature Expert — Host Config

## Role

Own the layered HOST CONFIG: one versioned key schema, per-user values, env
overrides. Keep host facts (job ceiling, worker memory, cpu family/features,
os, LLVM root/version, gpu) out of scripts and tracked files.

## Pipeline Links

- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)

## Feature Links

- Guide: `doc/07_guide/infra/toolchain/host_config.md`
- Versioned defaults (values commented): `config/host/host_config.sdn`
- Shell reader/generator: `scripts/setup/host-env.shs` (`--get`, `--print`, `--init`, `--selftest`)
- Simple reader: `src/lib/common/config_core/host_config.spl`
- Consumers: `scripts/bootstrap/bootstrap-build-jobs-policy.shs`,  `scripts/setup/platform-detect.shs`, `scripts/setup/llvm-toolchain-env.shs`,
  `CpuFeatureSet.from_host_config` in `src/lib/nogc_sync_mut/simd/host_cpu_config.spl`
- Setup hook: `scripts/setup/setup.shs` runs `host-env.shs --init`
- Spec: `test/01_unit/lib/common/config_core/host_config_spec.spl`

## Load-bearing facts

- Precedence: `SIMPLE_HOST_<KEY>` env > `${SIMPLE_HOST_CONFIG:-~/.config/simple/host.sdn}`
  > `config/host/<hostname>.sdn` > `config/host/host_config.sdn` > consumer built-in.
  More specific consumer vars (`SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS`,
  `SIMPLE_LLVM_WIN_ROOT_23`, `SIMPLE_LLVM_VERSION`) still beat the host config.
- Never put a real host value in `config/host/host_config.sdn`; it is
  documentation. `--init` never overwrites an existing user file.
- Bootstrap queries via `--get` in a child shell: every `SIMPLE_*` env var is
  folded into the native-build environment fingerprint, so exporting host
  values into bootstrap would churn caches.
- `llvm_version` is a major only (`23`); the Unix selector looks for `clang-<v>`.
  `llvm_root` picks no driver: clang-cl is Windows-MSVC-lane only, never a
  shared default.
- Cache keys (`cache_root`, `cache_scope`, `frontend_cache`, `hir_cache`,
  `native_build_cache_dir`, `cache_max_bytes`, `cache_max_gb`) are DEFAULTS for
  existing consumer vars (`SIMPLE_HOST_CACHE_ROOT`, `SIMPLE_CACHE_SCOPE`,
  `SIMPLE_FRONTEND_CACHE`, `SIMPLE_HIR_CACHE`, `SIMPLE_NATIVE_BUILD_CACHE_DIR`,
  `SIMPLE_CACHE_MAX_BYTES`, `SIMPLE_CACHE_MAX_GB`); a set consumer var wins.
  Applied only by `eval "$(host-env.shs --cache-env)"` /
  `host_config_apply_cache_env`; `host_config_load` (sourcing) skips all cache
  keys because `SIMPLE_HOST_CACHE_ROOT` is a live consumer; bootstrap never
  applies them (centralized storage sets `SIMPLE_CACHE` first). They may
  pick dirs/lane/on-off/caps, never disable producer keying or lane
  partitioning; `cache_scope` is validated as a single dir segment.
  Twin tables: `host_config_cache_var` in both readers (selftest case g, spec
  "cache keys").
