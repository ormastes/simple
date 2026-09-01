# Vulkan native strided round-trip validation — 2026-08-12

## Result

`PARTIAL`: exact packed strided buffer transfer works on the host Vulkan CPU
implementation. This is correctness evidence only; it is not physical-GPU or
8K/80 performance evidence.

## Native evidence

- Revision: `5617240a7ea` plus concurrent uncommitted Vulkan transfer work.
- ICD: `/usr/share/vulkan/icd.d/lvp_icd.json` (llvmpipe CPU Vulkan).
- Command:

  ```sh
  VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
    CARGO_TARGET_DIR=/dev/shm/simple-vk-runtime-target \
    cargo test -p simple-runtime --features vulkan \
    native_vulkan_strided_round_trip_preserves_surrounding_rows \
    --lib -- --ignored --nocapture
  ```

- Result: `1 passed; 0 failed`; test execution time `37.74s`.
- Oracle: two packed three-byte rows were uploaded at non-contiguous device
  offsets, read back through both strided APIs, and compared exactly. Bytes
  outside both regions retained the sentinel value.

## Remaining gate failures

- `test/01_unit/check/vulkan_damage_transfer_contract_spec.spl`: `1/2` passed.
  Its first source assertion requires `pub fn download_range(`, while the
  implementation exposes `download_strided` and constructs multiple
  `vk::BufferCopy` regions in one staging transfer. The owner must reconcile
  the intended API contract before promotion.
- Device is llvmpipe, not a physical GPU.
- No 7680x4320 viewport measurement, p50/p95 frame time, RSS, production
  presentation receipt, fallback receipt, or framebuffer checksum was produced.
- Therefore this row does not establish Vulkan 8K/80 capability.
