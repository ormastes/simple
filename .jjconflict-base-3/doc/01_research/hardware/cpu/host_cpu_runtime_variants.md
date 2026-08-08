# Host CPU Runtime Variants — Local Research

- `simple-simd` already owns the canonical `SimdTier` enum, compatibility ordering, fallback ordering, and raw host detection.
- `simple-compiler` currently chooses the active tier from `SIMPLE_SIMD_TIER` or raw `detect_profile()`.
- `simple-native-loader` currently loads only the unsuffixed runtime library name.
- SPK manifest metadata currently carries only one `{ target_triple, simd_tier }` variant and has no runtime-variant index.
- `simple-runtime` and `simple-loader` both embed package reader/format code, so manifest changes must be mirrored.

