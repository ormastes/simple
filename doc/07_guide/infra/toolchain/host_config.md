# Host Config — one versioned schema, per-user values

Host facts (worker counts, CPU family and ISA extensions, OS, LLVM location,
GPU) live in one layered config. The tracked file documents the keys; your
machine's values live in your own untracked file.

## Files and precedence

Highest wins:

| # | Layer | Location | Tracked |
|---|-------|----------|---------|
| 1 | environment | `SIMPLE_HOST_<KEY>` (e.g. `SIMPLE_HOST_MAX_BUILD_JOBS=8`) | — |
| 2 | user/host | `${SIMPLE_HOST_CONFIG:-$HOME/.config/simple/host.sdn}` (`USERPROFILE` when `HOME` is unset) | no |
| 3 | legacy per-host | `config/host/<hostname>.sdn` (`host_env:` block, hostname-checked) | yes |
| 4 | versioned defaults | `config/host/host_config.sdn` — every key present but **commented out** | yes |
| 5 | consumer built-in | e.g. job ceiling 16, worker memory 3300 MiB | — |

Do not edit `config/host/host_config.sdn` for your machine. Put values in your
user file, or export the env var for one shell. The user file sits next to the
existing per-user `~/.config/simple/config.sdn` (environment-variant policy),
which uses the same env-over-user order.

## Keys (`host_config:` block, two-space `key: value`)

| Key | Example | Consumer |
|-----|---------|----------|
| `max_build_jobs` | `16` | bootstrap worker ceiling (`bootstrap-build-jobs-policy.shs`); `SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS` still wins |
| `max_threads` | `32` | detected logical CPUs (informational) |
| `worker_mem_mib` | `3300` | bootstrap memory clamp; `SIMPLE_BOOTSTRAP_WORKER_MEM_MIB` still wins |
| `tree_rss_base_mib` | `3072` | process-tree RSS cap reserve (`scripts/bootstrap/lib/tree-rss-policy.shs`); `SIMPLE_BOOTSTRAP_TREE_RSS_BASE_MIB` still wins |
| `tree_rss_per_job_mib` | `96` | process-tree RSS cap budget per native-build worker; `SIMPLE_BOOTSTRAP_TREE_RSS_PER_JOB_MIB` still wins |
| `tree_rss_host_pct` | `50` | process-tree RSS cap ceiling as % of host physical RAM (1..75); `SIMPLE_BOOTSTRAP_TREE_RSS_HOST_PCT` still wins |
| `cpu_family` | `x86_64` / `aarch64` / `riscv64` | `CpuFeatureSet.from_host_config` |
| `cpu_features` | `sse2,sse4.2,avx,avx2,fma,bmi2` / `neon,sve` / `rvv` | `CpuFeatureSet.from_host_config` |
| `os` | `windows` / `linux` / `macos` / `freebsd` / `simpleos` | informational |
| `llvm_root` | `/usr/lib/llvm-23`, `C:/…/clang+llvm-23.1.1-x86_64-pc-windows-msvc` | `platform-detect.shs` LLVM discovery (tried first), `llvm-toolchain-env.shs` (Windows root, Unix PATH) |
| `llvm_version` | `23` (major only) | `llvm-toolchain-env.shs` preferred major; `SIMPLE_LLVM_VERSION` still wins |
| `gpu` | `on` / `off` | informational |

`llvm_root` is a prefix only and selects no compiler driver: clang-cl is used
solely by the Windows MSVC lane; Linux/macOS/FreeBSD/SimpleOS use clang/cc and
MinGW a target-qualified clang.

### Cache keys

Each cache key is only a **default** for one existing consumer variable; when
that variable is set it wins (the key is not applied). They choose dirs, the
lane name, on/off and size caps — never keying: cache entries stay
content+producer keyed and lane-partitioned
(`doc/05_design/compiler/incremental_build/per_lane_private_caches.md`).

| Key | Example | Consumer variable it defaults |
|-----|---------|-------------------------------|
| `cache_root` | `~/.cache/simple` | `SIMPLE_HOST_CACHE_ROOT` (host-shared CAS base; `SIMPLE_CACHE` / `SIMPLE_USER_STORAGE_ROOT` still win) |
| `cache_scope` | `default` | `SIMPLE_CACHE_SCOPE` / `--cache-scope`; `[A-Za-z0-9._-]`, no leading `.` |
| `frontend_cache` | `on` / `off` | `SIMPLE_FRONTEND_CACHE` (`off` = `0`) |
| `hir_cache` | `on` / `off` | `SIMPLE_HIR_CACHE` (`off` = `0`) |
| `native_build_cache_dir` | `~/.cache/simple/native-build/v1` | `SIMPLE_NATIVE_BUILD_CACHE_DIR` |
| `cache_max_bytes` | `10737418240` | `SIMPLE_CACHE_MAX_BYTES` (L2 GC / cache-dir evictor) |
| `cache_max_gb` | `20` | `SIMPLE_CACHE_MAX_GB` (`simple clean` auto mode) |

Apply them to an interactive shell with
`eval "$(sh scripts/setup/host-env.shs --cache-env)"` (or call
`host_config_apply_cache_env` after sourcing). Sourcing host-env exports no
cache key at all — not even `SIMPLE_HOST_CACHE_ROOT`, which `cache_root.spl`
reads live — so `run-phase1-local.shs` and other sourcing entrypoints keep an
unchanged `machine_cache_root()`. Bootstrap never applies them:
`bootstrap-from-scratch.sh` sets `SIMPLE_CACHE` via centralized storage before
the host-shared cache helper runs, and pins its own lane caches. A native
binary started without the eval does not read the file.
`--init` writes all cache keys commented with this host's defaults, so a fresh
setup changes no cache env.

## Commands

```bash
sh scripts/setup/setup.shs                 # first setup also writes your user file
sh scripts/setup/host-env.shs --init       # write it now (never overwrites)
sh scripts/setup/host-env.shs --init --all-cores  # opt in to all detected CPUs
sh scripts/setup/setup-freebsd-host.shs   # FreeBSD-only all-core initializer
sh scripts/setup/host-env.shs --print      # effective value + winning layer per key
sh scripts/setup/host-env.shs --get llvm_root
eval "$(sh scripts/setup/host-env.shs --cache-env)"   # cache defaults for unset vars
sh scripts/setup/host-env.shs --selftest   # fixtures incl. env > user > host > default
. scripts/setup/host-env.shs               # export SIMPLE_HOST_<KEY> (non-cache keys) into this shell
```

`--init` detects: CPU count (`getconf`/`nproc`/`sysctl`), family and features
(`/proc/cpuinfo` on Linux and Git Bash/MSYS, `sysctl machdep.cpu.*` on macOS,
`/var/run/dmesg.boot` on FreeBSD; SimpleOS gets the family baseline), OS via
`platform-detect.shs`, LLVM via `platform-detect.shs` then `llvm-config`
probes (including `~/.simple/toolchains/llvm-msvc-*`), and GPU via
`nvidia-smi` or `/dev/dri`.

`--init --all-cores` also sets `max_build_jobs` to the detected positive CPU
count. Plain `--init` keeps the consumer's default job ceiling. Both forms keep
an existing user file unchanged; edit that file explicitly to change an existing
configuration. The FreeBSD helper calls the same initializer and accepts no
arguments. Linux (including ARM64 Spark hosts) uses `host-env.shs` directly.
The canonical FreeBSD QEMU bootstrap wrapper initializes this file after source
sync and toolchain setup, using its selected guest build user's HOME. Smoke mode
does so only when the guest already contains the setup script. The full lane's
Stage 2 build requests `--jobs=full`, bounded by guest CPU allocation and the
user's job ceiling; existing memory limits still apply. Stage 3/4 resume keeps
its required `--jobs=1` orchestration contract.

The generated `worker_mem_mib` remains commented out, retaining the consumer's
3300 MiB per-worker estimate and memory clamp. Selecting all cores raises the
CPU ceiling; available memory still limits actual workers. LLVM and GPU values
come from the existing local probes, not from the all-core option. `gpu: on`
records detected host availability and does not enable an unsupported backend.

Bootstrap reads `max_build_jobs` / `worker_mem_mib` with `--get` in a child
shell. Before projecting its scratch HOME, centralized storage binds
`SIMPLE_HOST_CONFIG` to the original user's config path, preserving an explicit
`SIMPLE_HOST_CONFIG` override. Individual `SIMPLE_HOST_<KEY>` values are not
exported; subprocess readers continue to resolve the configured layers.

## Simple-side reader

`std.common.config_core.host_config` resolves the same layers on the shared
`config_core` engine (`vendor` = defaults, `machine` = per-host, `user`,
`session` = env). It is pure: callers pass the document texts and an env
snapshot. Spec: `test/01_unit/lib/common/config_core/host_config_spec.spl`.
