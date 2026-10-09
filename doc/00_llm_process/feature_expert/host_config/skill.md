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
- Consumers: `scripts/bootstrap/bootstrap-build-jobs-policy.shs`,
  `scripts/setup/platform-detect.shs`, `scripts/setup/llvm-toolchain-env.shs`,
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
