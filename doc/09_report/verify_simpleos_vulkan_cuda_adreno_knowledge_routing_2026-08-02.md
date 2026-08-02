# Verification: SimpleOS Vulkan/CUDA/Adreno and Knowledge Routing

Date: 2026-08-02

## Passing evidence

- CUDA processing adapter unit scenarios: 4/4.
- Vulkan/Adreno port unit scenarios: 7/7.
- Vulkan host-offload processing adapter scenarios: 3/3.
- QEMU staged typed-evidence scenario: 1/1.
- Canonical QEMU guest probe constructs `ProcessingIr` and routes both CUDA and
  Vulkan through `ProcessingDevicePort`, emitting `host-offload` provenance.
- UNO Q default fail-closed environment gate: 1/1.
- QEMU passthrough checker self-test and shell syntax: pass.
- Knowledge selector unit scenarios: 4/4.
- Knowledge-routing process integration scenarios: 2/2.
- VirtIO-GPU Venus protocol admission scenarios: 4/4. This proves feature,
  capset, context, blob, submit, and fence planning only; it is not native
  Vulkan execution evidence.
- VirtIO-GPU Venus wire scenarios: 8/8 provisional. They prove exact packed
  little-endian capset/context/blob/submit/map request bytes and typed rejection
  of truncated, error, type/flag-invalid, missing/mismatched-fence, and
  unexpectedly fenced responses. They do not prove a live control queue.
- Bounded Venus controlq admission/source-boundary scenarios: 4/4 provisional.
- Typed Venus environment discovery scenarios: 6/6 provisional.
- Decision-inventory coverage: 110/112 outcomes, 98%, gate 2/2.
- QEMU generated manual: complete, 116 lines, 0 stubs, 0 warnings.
- UNO Q generated manual: complete, 125 lines, 0 stubs, 0 warnings.
- Direct-env working/staged guards: pass.
- Rendering source-coupling guard: pass.
- Generated-spec layout: zero executable specs under `doc/06_spec`.
- Working numbered-artifact guard: pass.

## Correctly incomplete native rows

- Direct guest Vulkan/CUDA: blocked. The installed QEMU 8.2 and broken
  `virtio-gpu-gl` path cannot provide Venus. SimpleOS now owns fail-closed
  Venus feature/capset/context/blob admission, exact little-endian request
  encoding, and typed response/fence validation, but still lacks a live
  admitted feature/config discovery, shared-memory mapping, generalized queue
  ownership, a Vulkan ICD, real device completion,
  and native readback. The canonical producer remains classified
  `host-offload-only`.
- UNO Q SimpleOS-native Adreno: blocked. The staged adapter does not promote
  beyond board-Linux readiness until firmware, MMU/cache, queue, fence,
  device-origin readback, and display ownership are implemented and observed.

Resume UNO Q with:

`SIMPLEOS_UNO_Q_ADRENO_LIVE=1 bin/simple test test/03_system/os/board/uno_q_adreno_turnip_live_spec.spl --mode=interpreter --no-session-daemon`

Expected receipt:
`build/test-artifacts/03_system/os/board/uno_q_adreno_turnip_live/receipt.env`.

## Failures and limitations

- The deterministic selector initially exposed an older-parser collision with
  the local identifier `feature`; renaming it and restoring supported indexed
  array assignment resolved the defect. Its focused unit and integration specs
  now pass, but still through the bootstrap-seed runner described below.
- The isolated workspace has no accepted deployed pure-Simple runtime. GPU
  focused tests used a bootstrap-seed runner with isolated `SIMPLE_LIB`, so
  they are development evidence rather than final self-host qualification.
- SPipe docgen likewise produced complete provisional manuals through the
  bootstrap-seed runner; the artifacts are reviewed but do not satisfy the
  pure-Simple release docgen gate.
- Runtime instrumentation still emits no attributable counters. NFR-003 is
  instead proven for new owned decisions by the fail-closed tracked decision
  inventory: 110/112 outcomes (98%). The two uncovered live-MMIO outcomes are
  explicit and cannot be promoted by adding marker-only witnesses.
- Staged variants of git-oriented guards are incompatible with this jj-only
  workspace (`git diff --cached`); their working variants passed.

## Requirement audit

- REQ-001..005: implemented as staged contracts; native rows remain active.
- REQ-006..009: documents, registry, selector, receipt, cross-agent process
  updates, and focused executable verification exist.
- REQ-010: fail-closed blocker rows and UNO Q resume metadata exist.
- NFR-001..002, NFR-004..008: source/test contracts exist; native evidence and
  pure-selfhost qualification remain incomplete where stated.
- NFR-003: passed for new owned decisions through the 98% decision inventory.

## Next bounded implementation seam

Extend the existing bounded controlq seam with descriptor lifetime, distinct
queue-full/timeout/reset results, used-ring length/ID validation, and safe PCI
DEVICE_CFG/SHM discovery backed by kernel BAR grants. Native promotion
still additionally requires a Venus-capable QEMU/virglrenderer host, negotiated
capset and blob/context features, a compatible SimpleOS Vulkan ICD, mapped
shared memory, real fenced submission, and device-origin readback. UNO Q still
requires physical-board firmware/MMU/cache/queue/fence/readback/display proof.

STATUS: FAIL
