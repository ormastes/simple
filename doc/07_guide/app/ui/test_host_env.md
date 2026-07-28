# Test Host Environment

Run the aggregate after the canonical host gates. These are the same commands
retained in each blocked JSON row, so an operator can copy a row's
`resume_command` without translating it:

```sh
scripts/check/check-linux-hosted-wm-live-window-evidence.shs
sh scripts/check/check-cpu-simd-engine2d-evidence.shs
CPU_SIMD_ARCH_MATRIX_TARGET_BUILD=1 sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing && GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-run-current scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
bin/simple run src/app/test/test_host_env.spl -- --format=json
```

The `arm_simd` and `riscv_simd` rows share the architecture-matrix resume
command. The `display_input` and `framebuffer_readback` rows share the live
window command. The Vulkan command deliberately produces browser backing and
the current direct run; running only `--run` does not populate every retained
path admitted by `test_host_env`.

## Three distinct RenderDoc lanes

[Simple RenderDoc](../../../glossary.md#simple-renderdoc) means the repo-native
Simple 2D RenderDoc Backend Equivalence capsule: deterministic render records,
exact diff/equivalence, QEMU or board receipts, and pure-Simple inspection of
external capture contents. It is not a RenderDoc fork and it is not the
external `renderdoccmd` application or a wrapper around it.

The `renderdoc` host row above is the external RenderDoc-on-Simple-Vulkan gate.
The `--renderdoc-simple` setup option uses the external RenderDoc runtime/API
to capture the Simple Vulkan application, then runs
`check-renderdoc-simple-gate.shs`. Despite those names, this gate is not the
repo-native Simple RenderDoc counterpart.

The original Chrome HTML/CSS external-host lane is a third, separate lane. It
wraps the Chrome HTML/CSS producer with external RenderDoc and is resumed with:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs
```

See the [capture infrastructure guide](../../tooling/renderdoc_capture_infra.md)
for their shared artifact schema and distinct capture commands, and the
[SPipe/LLM Simple RenderDoc wiki](../../../00_llm_process/feature_expert/simple_renderdoc/skill.md)
for ownership and current gaps.

## Prepared-host prerequisites and postponement

- Use a source-matched deployed pure-Simple release binary. A Rust seed,
  translated execution, or a compiler from another source revision cannot
  promote a row.
- The live-window rows require a real Linux X11 display and screen-originated
  input. Screenshots or synthesized receipts are not substitutes.
- The SIMD shell must match the executed ISA: x86_64 for AVX2/SSE4.2, AArch64
  for NEON, or RISC-V for RVV. Cross-ISA QEMU remains correctness evidence, not
  a `native_host` pass.
- Vulkan requires a working device/driver plus the browser-backing and direct
  device-readback producers. The external RenderDoc-on-Simple-Vulkan gate also
  requires the external RenderDoc runtime/API to be installed and visible to
  the wrapper. The Chrome HTML/CSS external-host lane requires its prepared
  Chrome and external RenderDoc host.
- Do not add passwords, tokens, or credentials to a resume command or retained
  env file. Host setup credentials stay outside repository evidence.

Unavailable physical-host, QEMU, Metal, DirectX, and CUDA rows remain
postponed—not complete—until their prerequisites exist. Use the exact prepared
host commands and artifact checklist in the
[SimpleOS QEMU external-host resume matrix](../../../03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md#resume-matrix)
and the [QEMU postponement contract](../../platform/simpleos/qemu_system_tests.md#external-host-postponement-and-resume-contract).
The authoritative cross-host completion matrix is
[TODO317](../../../08_tracking/feature/wm_gui_web_2d_host_environment_acceptance_evidence_2026-07-28.md).

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

Browser parity additionally binds the Electron, Chrome, and Simple ARGB JSON
files and all three pairwise PPM diff files to producer-emitted lowercase
SHA-256 values. The aggregate reopens each current path only after a
regular-file, no-follow check and rejects missing, changed, malformed,
duplicate, or symlink-substituted artifacts before the Vulkan row can pass.

The Linux live-window gate injects the event at X11, records WM targeting,
dispatches the content-local point through the hosted BrowserSession, applies
the application mutation, updates authoritative window content, and captures
the resulting canonical Engine2D frame. The `display_input` row passes only
when the overall, input-receipt, semantic, text, replay-rejection, frame-marker,
and frame-correlation statuses pass; the origin is `screen`; event and WM target
IDs are positive; the semantic target is exactly `host-proof`; and callback and
mutation counts are exactly one. A partial three-field receipt no longer passes.

Before capture, the same admitted artifact and self-hosted runner must pass all
seventeen focused browser scenarios: HTML/CSS, animation, controls, native
controls/form submission, Tab/Shift+Tab focus traversal,
default-cancellation, Reload/Home, page-link, Favorite, stopped navigation,
unsupported document content, Node/native denial, oversized-protocol denial,
sandbox, scheme denial, admitted renderer crash/timeout containment, and
renderer lifecycle.
After the live event and present, an eighteenth focused gate validates the
single admitted input-to-present receipt; it is not percentile or FPS evidence.
