# Test Host Environment

Run the aggregate after the canonical host gates:

```sh
scripts/check/check-linux-hosted-wm-live-window-evidence.shs
CPU_SIMD_ARCH_MATRIX_TARGET_BUILD=1 sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
scripts/check/check-renderdoc-simple-gate.shs
bin/simple run src/app/test/test_host_env.spl -- --format=json
```

The JSON schema is `simple-test-host-env-v1`. Its required rows are
`x86_simd`, `arm_simd`, `riscv_simd`, `vulkan`, `renderdoc`,
`display_input`, and `framebuffer_readback`.

`pass` means retained native proof satisfied the row. `blocked` names the
missing host prerequisite and exact resume command. Cross-ISA emulation,
fallback rendering, CPU-mirror readback, screenshots, and invalid `.rdc`
artifacts do not satisfy a row.

The command always writes the structurally valid JSON report, but exits zero
only when every required row is `pass`. Any `blocked`, `fail`, malformed,
missing, duplicate, or unknown row keeps the aggregate gate nonzero.

Every SIMD row reads one complete architecture-owned rendered-frame receipt:
x86 uses AVX2 or SSE4.2, ARM uses NEON, and RISC-V uses RVV. Admission requires
native execution, bit-exact scalar parity, positive frame/per-operation/diagram
checksums and hits, equal expected/actual checksums, zero mismatches, the
no-blur/no-tolerance policy, and lower-hex SHA-256 identities for the canonical
evidence source, selected Simple compiler, and recomputed frame receipt. ARM
and RISC-V consume their exact matrix child `evidence.env`; aggregate substring
markers and capability-only probes cannot pass. The receipt records and hashes
whether its source shell architecture matched the executed ISA. Retained
`native_host` receipts may be aggregated anywhere; QEMU/emulated receipts stay
blocked.

The architecture-matrix source contract also binds the public Engine2D fill
and copy entrypoints to their RVV implementations. Merely retaining RVV helper
functions or intrinsics is insufficient: disconnecting either call reports
`missing-riscv-fill-dispatch` or `missing-riscv-copy-dispatch` and fails the
matrix. Tests may point `CPU_SIMD_ARCH_MATRIX_RUNTIME_SOURCE` at a mutated copy
to calibrate this failure; normal evidence leaves it unset.

The Vulkan row accepts only the canonical readback report with an overall and
spec status of `pass`, Vulkan availability/backend identity, exercised present
and readback paths, positive clear/rectangle pixel counts, exact expected and
actual checksums, zero mismatches, successful device readbacks, stable positive
device identity, no blur/tolerance, and zero strict/parity exit codes.
Missing, duplicate, synthetic, CPU-mirror, unsigned-zero, signed, or malformed
fields fail closed.

The Linux live-window gate injects the event at X11, records WM targeting,
dispatches the content-local point through the hosted BrowserSession, applies
the application mutation, updates authoritative window content, and captures
the resulting canonical Engine2D frame. The `display_input` row passes only
when the overall, input-receipt, semantic, text, replay-rejection, frame-marker,
and frame-correlation statuses pass; the origin is `screen`; event and WM target
IDs are positive; the semantic target is exactly `host-proof`; and callback and
mutation counts are exactly one. A partial three-field receipt no longer passes.
