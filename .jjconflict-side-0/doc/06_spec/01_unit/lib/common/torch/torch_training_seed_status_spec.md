# Spec: Torch Training Seed Status

Source: `test/01_unit/lib/common/torch/torch_training_seed_status_spec.spl`

## Behavior

- GC async, NoGC async, and NoGC sync Torch training helpers expose
  `set_seed(seed) -> text` and `manual_seed(seed) -> text`.
- The helpers return `unsupported` while no owner runtime SFFI manual-seed
  symbol exists.
- The old silent no-op prose and comments are absent.
- `manual_seed` delegates to `set_seed` so both helpers report the same status.

## Covered Requirement

- Torch seed helpers must be functional or explicitly unsupported; they must not
  silently claim deterministic seeding when the runtime owner does not expose
  that capability.

## Not Covered

- Real `rt_torch_manual_seed` runtime support.
- Deterministic random tensor parity after seeding.
- CUDA-device-specific manual seed behavior.
