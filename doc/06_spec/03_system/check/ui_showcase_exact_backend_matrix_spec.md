# UI showcase exact backend matrix

Source: `test/03_system/check/ui_showcase_exact_backend_matrix_spec.spl`.

Run `sh scripts/check/check-ui-showcase-exact-backend-matrix.shs` with an
admitted self-hosted `SIMPLE_BIN`. The wrapper builds the exact Engine2D
showcase entry once with `SIMPLE_NO_STUB_FALLBACK=1`, rejects fabricated-stub
log markers, then runs software, scalar CPU, CPU-SIMD, and Vulkan everywhere,
plus Metal on Darwin.

Every backend must produce an exact non-fallback receipt and nonempty binary
PPM capture. CPU-SIMD additionally requires positive native SIMD hits. Metal
additionally requires device readback plus positive backend and device
identities. Vulkan uses its dedicated fail-closed DrawIR host and requires
fresh device readback, positive backend/device identities, and Vulkan text
execution instead of the generic host's fallback token.
`SIMPLE_SHOWCASE_BACKENDS` can select an explicit
comma-separated matrix for a targeted host.
