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

The x86 row reads the complete retained CPU-SIMD receipt rather than rerunning
a fill/copy mini-probe. It requires AVX2 or SSE4.2 native execution, bit-exact
scalar parity, positive native and per-operation hits, zero
fill/copy/alpha/edge/scroll/diagram mismatches, and the no-blur/no-tolerance
policy. The SIMD matrix separately retains architecture-specific executed-path
markers for x86 AVX/SSE, ARM NEON, and RISC-V RVV. QEMU parity is reported in
blocker reasons and artifacts, but only a native host can turn an ARM or
RISC-V row into `pass`.

The Vulkan row accepts only the canonical readback report with an overall and
spec status of `pass`, Vulkan availability/backend identity, exercised present
and readback paths, successful clear and rectangle device readbacks, positive
native backend handles and device identities, and a zero strict-spec exit code.
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
