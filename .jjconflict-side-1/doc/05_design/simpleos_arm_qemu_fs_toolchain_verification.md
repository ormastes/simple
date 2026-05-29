<!-- codex-design -->
# SimpleOS ARM QEMU FS Toolchain Verification Design

This design refreshes the ARM filesystem-backed QEMU lane around the current
toolchain contract rather than the older `hello_world.smf` probe narrative.

## Implementation-Facing Goals

- keep ARM64 and ARM32 on `arm64-virtio-fat32-smf` and
  `arm32-virtio-fat32-smf` as the default QEMU verification targets
- keep host-side validation strict about staged SMFs, manifests, lane metadata,
  and proof assets
- require guest serial evidence for `/sys/apps/simple_compiler`,
  `/sys/apps/simple_loader`, `/sys/apps/clang`, and `/sys/apps/rust`
- preserve per-arch guest quirks while unifying the acceptance scaffolding

## Verification Phases

### Phase 1: Shared Host Validation

Use one shared validation helper shape to build the ARM host-side image checks.

Expected responsibilities:

- select `build/os/fat32-arm64.img` or `build/os/fat32-arm32.img`
- assert required SMF markers for `simple_compiler`, `simple_loader`, `llvm`,
  `clang`, and `rust`
- assert manifest metadata for lane-specific `entry_app` and `lane=...` fields
- assert proof assets such as version files and toolchain pipeline steps

Expected marker naming:

- `SCOMPSMF`
- `SLOADSMF`
- `LLVMSMF`
- `CLANGSMF`
- `RUSTSMF`

### Phase 2: Shared Scenario Routing

Keep one shared ARM routing contract for:

- `get_qemu_target(Architecture.Arm64)` -> ARM64 fs-exec target
- `get_qemu_target(Architecture.Arm32)` -> ARM32 fs-exec target
- scenario disk-image selection by architecture
- scenario acceptance timeout and completion checks

The shared routing helper should expose the contract; it should not erase
architecture-specific QEMU flags or loader wiring.

### Phase 3: Shared Guest Assertion Set

Build the required ARM serial marker set from shared helpers, then let each
architecture produce those markers in its own way.

Required guest assertion families:

- `process-backed:ok` for `simple_compiler`
- `process-backed:ok` for `simple_loader`
- `process-backed:ok` for `clang`
- `process-backed:ok` for `rust`
- `vfs-app-read:ok` for the same four apps
- `native-toolchain-launch:ok` for `clang`
- `native-toolchain-launch:ok` for `rust`
- `TEST PASSED`

Keep `llvm` in the staged-image contract but do not make it the center of the
live ARM acceptance story.

### Phase 4: Reporting And Follow-Up Cleanup

Keep missing-marker reporting aligned with the shared marker helper so both ARM
lanes fail with the same verification vocabulary.

Planned cleanup:

- rename stale ARM helper comments that still claim the lane is only about
  `/sys/apps/hello_world.smf`
- isolate ARM32 text/trace quirks behind helper boundaries rather than letting
  them leak into the shared contract
- prepare the shared helper shape for later RISC-V and x86 reuse

## Test Design

Required unit coverage in `test/unit/os/qemu_runner_spec.spl`:

- the default ARM routing stays on fs-exec targets
- both ARM scenarios keep the correct disk paths
- the host validation command requires the staged ARM tool/app set
- shared ARM serial markers require the fs-launch evidence for both ARM32 and
  ARM64

Required live verification:

- `bin/simple os test --scenario=arm64-virtio-fat32-smf`
- `bin/simple os test --scenario=arm32-virtio-fat32-smf`
- `sh scripts/make_os_disk.shs 64 build/os/fat32-arm64.img "" arm64`
- `sh scripts/make_os_disk.shs 64 build/os/fat32-arm32.img "" arm32`

The design is complete only when metadata-only staging cannot accidentally pass
the ARM acceptance lane.
