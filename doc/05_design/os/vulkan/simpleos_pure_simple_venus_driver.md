<!-- codex-design -->
# Detail design: SimpleOS pure-Simple Venus session

Status: proposed implementation contract.  Production sources remain unchanged.

## Construction algorithm

`VenusSession.open(drv)` is a linear state machine.  It returns
`Result<VenusSession, VenusInitError>` only after every state transition has a
validated response.  The only permitted sequence is New → FeaturesNegotiated →
CapsetSelected → SharedMemoryMapped → RingReady.  Every failure runs the
inverse cleanup for already-owned resources and returns `Failed`; no partially
ready object escapes.

`VenusControlBuffer {request_virt:u64, request_phys:u64, response_virt:u64,
response_phys:u64, capacity:u64}` is exclusively owned by
`transport/control.spl`.  A request checks `request_len <= capacity`; response
parsing checks both descriptor-used length and command-specific minimum/max.
The initial implementation serializes controlq; it does not introduce a second
lock-free queue around an existing single mutable DMA buffer.

`VenusRing` uses unsigned monotonic sequence numbers.  A ring producer first
checks payload size, contiguous writable space, and `in_flight < 3`; only then
copies generated protocol bytes and issues SUBMIT_3D.  Fence ids are never
reused during the session.  Completion must match both fence id and ring index.

## Public-to-next-layer policy

The compositor constructs the provider only through
`VenusRenderProviderFactory.try_create(drv)`.  It receives one of
`Ready(VenusRenderProvider)` or `Unavailable(reason)`.  It may pass a sealed
DrawIR byte sequence to `submit_draw_ir`; it may not build Vulkan/Venus wire
commands.  `readback_exact` is test/capture-only and requires an expected
device-source token, so an in-memory CPU pixel list cannot satisfy the oracle.

## Test design

- Unit owner: capset size/version rejection, feature conjunction, SHM bounds,
  state transitions, ring full/wrap refusal, fence-ring mismatch, cleanup order.
- Protocol owner: fixture bytes generated/pinned from the exact upstream Venus
  revision; validate no invented opcode or field layout appears.
- QEMU system owner: capability transcript, actual capset id/version, session
  ready receipt, command fence, exact device readback pixels/checksum, and
  explicit `qemu_only` provenance.  A missing host feature is SKIP/UNAVAILABLE,
  never PASS.
- Compositor owner: selection remains CPU/rejecting before a real provider;
  after readiness it proves changed pixels through the provider receipt and
  fails when source/fence/readback provenance is absent.

Every initial SSpec helper is named up front: `setup_venus_fixture`,
`step_open_venus_session`, `step_submit_device_draw`, and
`check_device_readback_receipt`.  Before transport exists, these helpers must
be fail-fast (`fail("venus transport not implemented")`), never a placeholder
success assertion.
