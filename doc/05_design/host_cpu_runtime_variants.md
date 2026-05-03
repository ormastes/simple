# Host CPU Runtime Variants Design

## CPU Config

- Path:
  `dirs_next::cache_dir()/simple/host/<target-triple>/cpu_config.sdn`
- Override:
  `SIMPLE_CPU_CONFIG_PATH`
- Fallback:
  `~/.simple/cache/host/<target-triple>/cpu_config.sdn`

## Selection Rules

- Active tier precedence:
  1. `SIMPLE_SIMD_TIER`
  2. `cpu_config.sdn enabled.simd_tier`
  3. raw `detect_profile()`
- Default `enabled.simd_tier` uses the best currently implemented tier for the host family.
- `enabled.instruction_sets` is clamped to `support ∩ simple_support`.

## Loader Rules

- Probe suffixed sibling names first:
  `libsimple_runtime.<tier>.so`
  `libsimple_runtime.<tier>.dylib`
  `simple_runtime.<tier>.dll`
- Fallback to unsuffixed scalar/common runtime last.

