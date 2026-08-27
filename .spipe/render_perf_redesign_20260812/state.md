# Feature: render_perf_redesign_20260812

## Status

The render-performance redesign remains in progress. See
`doc/03_plan/ui/perf/render_perf_resume_matrix_2026-08-12.md` for current
admission gates and `doc/08_tracking/bug/self_hosted_runtime_authority_republish_path_2026-08-12.md`
for compiler authority evidence.

### Current reconciliation (2026-08-12)

- **F1 has focused seed-interpreter coverage.** The Rust seed interpreter now has a
  distinct `Value::ClassInstance` identity carrier with shared field mutation;
  value structs retain copy-on-write object fields. The focused Rust corpus
  covers direct/trait/optional/array/parameter/return class aliases plus a
  struct COW control, but its one run stopped before `simple-compiler`
  compilation on an unrelated `runtime/src/value/actors.rs` E0716 lifetime
  error. The actor lifetime error was resolved by its owner, and the canonical
  `interpreter_call::exec_function_with_self_value` import was restored. The
  focused `class_instance_interpreter_semantics` Rust test passes 1/1 for
  direct, trait, optional, array, parameter, and return aliases plus struct
  COW. JIT/native and provenance-matched self-hosted corpus evidence remain
  open, so F1 is not a performance promotion.
- The standalone Web damage adapter is now consumed by the persistent
  `Engine2dCompositorBackend` and all hosted Web entry points. Exact revision
  hits report NONE without rerasterization; LOCAL requires same producer
  generation, backend, transfer profile, prior complete result, and stable
  resources. The focused runner is still blocked before its spec by an
  unrelated bootstrap parser failure, so this is source-reviewed wiring rather
  than executed self-hosted parity evidence.

## Acceptance Criteria

- CPU blend spans retain scalar parity and remove row-buffer work; x86, ARM64,
  and RV64 have exactness receipts.
- Bare fill matrix is exact on x86/ARM64/RV64; booted scanout remains Stage-4
  gated.
- Vulkan retains presenter adapter/buffer ownership and direct-damage receipts.
- DrawIR, Web, GUI, and WM use canonical DrawIR and fail-closed NONE/LOCAL/FULL
  replay.
- The 8K harness emits one terminal receipt on every termination route.
- No 8K/80 promotion occurs without a fresh native p95<=12.5ms, checksum,
  known-completion, no-fallback receipt.
- Current plans retain historical evidence and exact resume commands.

## Current Evidence

- Public SoftwareBackend blend spans use the in-place native facade without row
  gather/scatter. Bounded x86 SSE2/AVX2, ARM64 NEON, and RVV bridges pass their
  direct C span-oracle gates; scalar overlap/tail fallbacks remain.
- Exact x86 C 7680-row blend receipt: opaque image 1.171x, opaque constant
  6.244x, mixed alpha 1.106x scalar. This is not an end-to-end 8K/80 claim.
- Bare fill exactness matrix passed for x86, ARM64, and RV64 QEMU-user paths.
- Web damage is consumed by the persistent compositor Engine2D cache at the
  hosted entry points; it exports fail-closed effective NONE/LOCAL/FULL
  metadata. The focused runner is blocked by an unrelated bootstrap parser
  failure, and outer WM/swapchain partial-present evidence remains open.
  Vulkan adopted-device retention and direct-present receipt plumbing remain
  separate mechanism work, not Web end-to-end evidence.
- Stage 3 linked 815 units with zero failures. Stage 4 also linked 815/0 but
  admission was withheld because compiled roots changed during the shared build;
  it was not deployed. Native Vulkan, booted SimpleOS, and 8K rows stay closed.
- Git HEAD equals origin/main, but the shared tree has over 1,000 mixed paths;
  no commit/push is safe.
- The SIMD provider fill operation now uses the in-place span ABI instead of a
  temporary returned row plus copy loop. The seed source check emitted only
  known global warnings; native execution awaits an admitted compiler.
- GUI benchmark rows now select only an admitted self-hosted compiler. Absent
  authority produces explicit unavailable rows instead of seed timeout noise;
  the focused Bash contract passes.
- Web post-DrawIR effective LOCAL/FULL plans now pass through overflow-safe
  compositor validation into the existing direct-present damage queue; NONE
  retains the no-transfer path. Invalid plans fail closed to an exact full
  viewport. Native partial-copy evidence still awaits authority admission.
- A stable-seal Stage-4 candidate subsequently linked but failed its
  essential-tools admission smoke: `validate_json_valid` sees `unknown command
  'run'`. This is now the concrete self-hosted CLI blocker; no deployment or
  native rendering gate was attempted.
- The isolated immutable full-CLI recovery then failed at phase 1 because
  `app.doc.public_check.statistics` resolves to an empty or excluded module.
  No full CLI artifact or admission receipt exists; the concrete compiler
  closure blocker is tracked before any authority retry.
- O2 multiscale damage is now consumed by the WM compositor through a persistent
  256/64/32 pyramid and `RetainedFrameSchedule`; only explicit measured profile
  admission reaches `Engine2D.present_retained_schedule`, otherwise existing
  full-present fallback remains. The focused seed-run test has no verdict.
- GUI now retains one Engine2D target per compatible window/backend instead of
  a second pixel cache; exact revisions reuse NONE, LOCAL replays canonical
  DrawIR damage in place, and lifecycle release is wired into window destroy.
- **F3 dirty metadata is now fixed-capacity.** `UiSceneColumnArenaV2` allocates
  dirty-range columns once from its total physical-row capacity, coalesces by
  indexed replacement, and resets only `dirty_len` across a swap. Its focused
  spec pins stable dirty-column lengths across warm commits and an interleaved
  range bridge. The available test runner still stops in an unrelated parser
  error before a verdict, so this is source-checked mechanism work only; F1
  cross-engine identity and F2 native-span criteria still block any zero-copy
  or performance promotion.
- **F3 partition leases are fixed-capacity too.** All five stable-lease columns
  are preallocated from total physical-row capacity; nonempty leases consume
  at least one row, and zero-row leases are refused. The focused source test
  now pins those column lengths as well. Its one runner invocation hits the
  same unrelated parser failure before a verdict.
- **F2 now has a non-permissive native admission gate.** The separate
  `packed_span_native_acceptance_spec` requires `native-packed-v1`, zero
  registry/C verdicts, and a nonzero stable base across repeated resolves; the
  older ABI/refusal spec remains deliberately scalar-or-native. Its one native
  invocation was blocked before execution by the shared MIR parser error, so
  it records the criterion rather than closing it. The actual Infer lowering
  repair is concurrently owned in the compiler and awaits its full
  entry-closure result.
- **Parser-repair evidence remains pending.** One attempted Stage-2-only
  `simple test ...parser_multiline_shape_parity_spec` invocation returned
  `unknown command 'test'`; that bootstrap compiler intentionally exposes no
  full CLI. It is not a negative parser result and must not be retried through
  that artifact. Use the eventual admitted full CLI for the focused regression.
- **F4 direct present is now frame-bound and fail-closed.** Healthy hosted
  Vulkan frames submit without normal readback only when they carry a fresh
  fenced submission generation, exact candidate frame revision, device buffer
  ownership, and presenter identity. Presentation consumes its candidate before
  any validation/WSI action, so failures cannot stale-retry; they explicitly
  read back and use the existing pixel path. Retained LOCAL clears prior
  override/receipt state before direct submit. The focused structural contract
  exits cleanly; live WSI/admitted native evidence is still required.
- **F4 PPM is explicit evidence export only.** `ScreenWmHost` defaults to no
  file writes, while `SIMPLE_WM_FRAME_EXPORT=1` produces PPM/sequence/receipt;
  its focused spec passes 2/2.
- **Authority remains pre-Stage-3/4.** An earlier Stage-2 sanity receipt failed
  `runtime_error_invalid_field_receiver_then_illegal_instruction` (status 132),
  while the tagged-receiver Stage-2 campaign is now separately admitted below.
  Parser/F2 focused subsets pass, but no Stage-3/Stage-4 full self-hosted
  compiler receipt exists. Do not invoke native rendering or relabel these
  mechanism checks as deployed evidence.
- **Tagged-receiver Stage 2 is now admitted.** Its immutable receipt records
  `status=pass`, stable candidate hash
  `a4bc8f44b74094b07d4c4dfbcb586ed291cbc89655464b6fba0a0c6f2b847e55`, and
  bootstrap-CLI frontend sanity. The run deliberately stopped before Stage 3;
  this is not a full CLI, Stage-4, deployment, or native-rendering admission.
- **Stage-3 resume now accepts that external admitted artifact safely.** The
  provenance resolver accepts only canonical repo paths or canonical children
  of `/mnt/data/.simple/bootstrap`, rejecting traversal, symlinks, aliases,
  and arbitrary absolute paths. Its focused shell test passes. A Stage-3 run
  still requires a frozen/quiescent source root: do not launch it from this
  actively changing shared worktree and invalidate its own source manifest.
- **Stage-3 recovery now preserves Stage-2 provenance bindings.** Before any
  lock or artifact mutation it compares current source, git state, and tool
  authority to the immutable admitted records; it never overwrites those
  records. Recovery archives use exclusive canonical per-attempt directories,
  and lock cleanup is owner-aware/signal-safe. This is source-reviewed and
  shell-syntax checked, but behavioral lock/mismatch fixtures and a frozen-root
  Stage-3 build remain required.
- **Stage-3 resume wrapper passed final static safety review.** Its external
  output resolver, immutable authority preflight, signal-safe owner lock, and
  collision-proof attempt archive have no remaining static must-fix finding.
  The wrapper remains intentionally unlaunched here because this shared root
  fails the admitted Stage-2 source/git binding; use a frozen matching checkout
  for the first behavioral resume and Stage-3 receipt.
- **The tagged-receiver Stage-2 parent can no longer be resumed.** Its admitted
  authority requires commit `5a42094a…`, tree `69a868c8…`, dirty fingerprint
  `33ad2bec…`, and a 12,606-entry source snapshot. The originating checkout
  has advanced and no scanned frozen worktree matches those identities. This is
  the expected fail-closed outcome: create a new frozen checkout and a fresh
  Stage-2 admission before the next Stage-3/4 campaign; never force this parent
  into a mismatched source tree.
- **O2 Web now has a producer-owned PaintChunk sidecar.** Canonical retained
  Web DrawIR results carry exact composition/batch membership, lockstep chunks,
  bounds, stable IDs, and a revalidator. Every visibility proof is UNKNOWN and
  culling is disabled, so this cannot affect pixels or become an accidental
  optimization; it is the required semantic source for a later fail-open
  compositor visibility consumer. The focused spec is source-hygiene checked
  but awaits an admitted Simple runner.
- **O2 sidecar revalidation is semantic, not geometric.** It retains an ordered
  collision-free snapshot of every composition, batch/source/embedding field,
  command field, and nested style/edge/point/glyph payload; changed text,
  style, clip, or image data with unchanged IDs/bounds is rejected. This fixes
  the stale-sidecar hazard before any future consumer can trust the metadata.
- **O2 sidecar is now opt-in, not a hot-path transport.** A review found that
  eagerly building/rebuilding its full arrays and semantic snapshot adds
  O(commands + nested payload) allocation/work while visibility culling is
  disabled. Production Web results, worker encoding, and hosted decoding carry
  only canonical DrawIR again. A future consumer must explicitly request
  `web_paint_chunk_frame_from_composition`, validate it, and prove a real
  visibility benefit before it can enter a frame path.
- **O2 sidecar validation pins all current producer columns.** The explicit
  builder’s matcher rejects stale semantic payloads and tampered sentinel
  property/cache columns; it is a correctness capability, not yet a retained
  runtime artifact.
- **G1 presenter per-image replay is bounded and exact.** The presenter retains
  32 successful damage transitions and replays their non-overlapping union for
  a stale acquired swapchain image; a focused no-WSI Rust test passes for a
  third-image replay and history eviction. This does not close G1: presenter
  WSI acquisition and presentation still require admitted native and live
  receipts before any hosted or live-present claim.
- **G1 pre-acquire compatibility and WSI-acquire recovery are now fail-closed.**
  The presenter rejects a buffer unless it is transfer-source capable and
  matches immutable BGRA8 width/height/stride/byte-length expectations and the
  live swapchain extent/format (focused no-WSI Rust tests: 2/2). A definitely
  unsubmitted acquire is drained only by an empty fenced queue submit; an
  unknown completion keeps the presenter registered and quarantined
  indefinitely (focused no-WSI Rust test: 1/1). These mechanisms do not
  provide a live WSI/native receipt, so G1 remains partial.
- **G1 interpreter dispatch is now an explicit feature-gated whitelist.** The
  compiler registers exactly the 13 Engine2D presenter symbols through a typed
  managed `[i64]` damage-array adapter; raw and prefix-wide routing are absent
  and legacy `gpu.rs` dispatch remains untouched. Its focused Cargo check is
  currently blocked before compilation by the external vendored `rspirv`
  `build.rs` absence, so this is a static boundary mechanism—not interpreter
  integration, archive linkage, or a live WSI receipt.
- **G1 high review reopened production readiness.** Current presenter teardown
  cannot recover after a WSI present, raw Winit handles have no lifetime lease,
  Engine2D compute writes are not synchronized to transfer reads, and
  resize/out-of-date handling only poisons the presenter. These are correctness
  blockers, not mere performance gaps: no G1 path may be promoted until a
  presenter-owned recovery/lifetime/synchronization repair has focused
  no-WSI coverage and a later admitted live receipt.
- **G1 now retains the Winit lifetime across presenter ownership.** The Winit
  runtime has a per-window surface lease, window destruction refuses while a
  lease is live, and the Simple presenter/compositor/host path keeps the
  presenter plus lease if close fails. Scoped diff hygiene passes. This repairs
  the raw-handle lifetime gap only; it has no compile/run receipt yet, and the
  producer-to-transfer completion dependency plus out-of-date recreation policy
  remain required before G1 can leave fail-closed mechanism status.
- **G1 recovery now distinguishes recreate requests from unsafe teardown.** A
  pre-acquire out-of-date result requests recreation without an acquired
  semaphore or permanent poison; acquire-suboptimal retains the definitely
  unsubmitted image for fenced consumption, and post-present suboptimal remains
  under WSI-completion-unknown quarantine. Further presents fail fast while
  recreation is requested. The focused no-WSI policy test passes 1/1; no
  in-place recreation or live WSI completion claim is made.
- **G1 synchronization implementation is under review, not accepted.** It
  introduces a one-shot exact framebuffer present-source lease and the required
  `COMPUTE_SHADER/SHADER_WRITE → TRANSFER/TRANSFER_READ` barrier, but its broad
  ABI/runtime/compositor wiring was interrupted before compile/testing. Review
  already found an independent presenter-lifecycle defect: successful present
  permanently marks WSI completion unknown, and Winit event-loop destruction
  bypasses the current window lease. These must be repaired before the new
  synchronization mechanism can be accepted.
- **G1 portable queue dependencies now compile.** The exact present-source
  lease owns a producer-ready semaphore; compute signals it after the fenced
  producer submission, graphics waits it together with swapchain acquire at
  transfer, then signals an image-keyed render-finished semaphore consumed by
  present. Completion-unknown paths retain every referenced semaphore, command,
  fence, and buffer. Vulkan library and test compilation pass, but the focused
  behavior test was interrupted by a fixed import error and was not rerun;
  this remains non-live mechanism work pending review and execution.
- **G1 still lacks a WSI retirement/recreate lifecycle.** The portable queue
  dependency chain is structurally correct, but a successful queue-present is
  conservatively marked completion-unknown forever and a recreate request only
  disables later presents. That leaks the presenter lease and leaves resize
  unusable. A capability-gated present-retirement mechanism plus a real safe
  swapchain-recreate owner transition is required before G1 can be accepted.
- **The first WSI lifecycle patch is interrupted and uncompilable.** Its
  present-fence method was placed under `Drop` instead of `VulkanSwapchain`,
  retirement fences are allocated too late to preserve an acquired transaction
  on allocation failure, and replacement swapchain construction is not yet
  commit-or-quarantine safe. These are active repair items; the direct presenter
  remains disabled/unadmitted until they are corrected and tested.
- **WSI runtime transaction safety has a bounded repair pending verification.**
  Present-retirement fences are now prepared before image acquisition and kept
  before queue-present, partial image-view construction cleans its prefix, and
  replacement creation no longer retires the current owner during a partial
  failure. The immediate method-placement compile repair passed, but final
  post-edit compile/test evidence is still absent; facade/host resize remains
  deliberately deferred.
- **The bounded WSI runtime transaction now compiles under Vulkan.** The
  replacement-image failure destroys its just-created raw swapchain, the
  recreate ABI no longer extends a mutex guard, and
  `cargo check --locked --offline -p simple-runtime --features vulkan --lib`
  passes (only an existing Winit deprecation warning). Focused transaction
  behavior tests, facade/host resize, and live WSI verification remain open.
- **WSI replacement now uses Vulkan's live old-swapchain contract.** Initial
  and replacement image/view setup destroy newly-created raw swapchains on
  every post-create failure. Replacement reports whether Vulkan has retired the
  current owner; the presenter then poisons rather than reuses that owner, and
  likewise retains a fully-created replacement only for teardown if later
  presenter-local allocation fails. A higher-model re-review passed after also
  adding a terminal retired-owner guard and moving provenance byte-size
  validation before replacement. The same offline Vulkan library check passes;
  behavior-test execution, facade/host resize, and live WSI verification remain
  pending, so G1 is still not admitted for live WSI.
- **One no-WSI retirement transaction test now passes.**
  `transactional_lifecycle_without_wsi_requires_retirement_before_acquire_and_present`
  passed 1/1 in `simple-runtime` with Vulkan enabled. It validates only the
  pure transaction ordering; it is not a window-system, physical-GPU, native
  archive, or performance receipt.
- **Current G1 Vulkan library compilation remains green after the lifecycle
  repair.** `cargo check --locked --offline --manifest-path
  src/compiler_rust/Cargo.toml -p simple-runtime --features vulkan --lib`
  completed with only the existing Winit deprecation warning. This confirms
  the Rust library surface, not native-archive linkage, WSI, physical-adapter,
  or performance behavior.
- **Stage-3 recovery retains future failed candidates as evidence.** Before a
  resumed build removes a previous candidate it archives a regular-file copy
  with a rehashed SHA-256 and immutable source/git/tool-authority hashes. The
  EXIT path attempts the same retention for an interrupted or failed new
  candidate and reports an archival failure instead of silently claiming it.
  These archives are diagnostic only and cannot act as authority or deployment
  inputs. Shell syntax, output-path contract, and diff hygiene pass.
- **F2 inferred folded-constant lowering has been scope-reviewed.** The
  `mir_const_value_type` helper plus the module-constant and mutable-static
  Infer branches are the criterion-7 change. They must be accepted separately
  from current unrelated `Result` lowering and `verification_contract`/positional
  `HirFunction` hunks in the same dirty files; no native F2 result is claimed
  until that split and the admitted native packed-span gate run.
- **O2 Web now retains producer-attested opaque-proof metadata.** The canonical
  HTML DrawIR producer emits exact proofs only for its explicitly marked
  primary node rectangle after checking opaque colour, full ancestor/batch
  opacity, unfiltered/no-image/no-gradient/no-radius/no-border/no-shadow
  style, exact viewport/clip containment, and bounded ancestry. Canvas,
  overlays, scrollbar chrome, placeholders, image/text/embedded batches, and
  any ambiguous condition are UNKNOWN. The final proof vector is composition
  order-aligned and binds command, batch, surface and embedding state; culling
  remains hard-disabled. Higher-model review passed this boundary. Focused
  execution remains blocked by the non-admitted runner.
- **Cycle 7 Stage 2 is newly admitted, but not resumable from this tree.**
  `/mnt/data/.simple/bootstrap/fv2-context-authority-20260812/cycle7` now has
  `stage2-sanity.env` with `status=pass`, a stable candidate SHA, and
  `runtime-admitted.txt`; the earlier Cycle 6 invalid-field-receiver candidate
  remains diagnostic-only and was not retained. Cycle 7's frozen source
  worktree is clean, but its pinned resume script predates the provenance and
  lock-safety repairs (it re-snapshots admitted bindings and uses unsafe
  lock cleanup). The live shared source tree also has 281 dirty paths under
  `src/compiler`, `src/app`, and `src/lib`, so it cannot substitute for the
  frozen source/git/tool binding. Do not deploy, use, or resume until a
  quiescent matching worktree has a matching provenance-safe resume toolchain.
- **G1 Winit leases are now token-bound.** Each lease has a process-unique
  opaque token; only its exact `(window, token)` pair may release it, and both
  window and event-loop teardown refuse while any lease remains. Presenter
  close enters a fail-closed requested state and retains its handle/token if
  destruction cannot prove safety. The Winit test target compiles and focused
  diff checks pass; the post-fix unit-test execution was intentionally not
  retried after its one allowed run exposed a compile fix.

- Conservative PaintChunk occlusion remains intentionally unintegrated. The
  legacy positional PaintChunk→DrawIR delta path has index-replacement only,
  so it cannot itself remove a hidden command. The additive stable DrawIR patch
  transaction now carries target batch templates/counts and atomically applies
  insert/remove/reorder updates without collapsing batches (focused bootstrap
  seed spec: 14/14). It still has no retained PaintChunk producer/caller and
  no producer-derived opaque proof, so culling remains disabled.
- The new canonical full-frame PaintChunk lowerer validates one producer-owned,
  nonempty unique stable ID per chunk, checked i32/ARGB rectangles, and source
  order before emitting DrawIR. Its focused bootstrap-seed interpreter spec
  passes 4/4. It intentionally has no production caller, no removal transaction,
  and no occlusion input; it is a prerequisite mechanism, not an O2 completion
  or performance claim.
- `engine2d_draw_ir_render_damage_with_images` now supplies the retained-target
  executor seam: it requires a checked non-overlapping LOCAL plan, rejects
  parent-sampling commands, clears every accepted old/new region, replays the
  full flat display list under that clip, submits once, and returns the updated
  Engine2D explicitly. Bootstrap-seed focused parity/rejection coverage passes
  2/2. No compositor has supplied an admitted schedule to it yet.
- GUI content frames now own bounded per-window CPU Engine2D targets (at most
  eight entries and one 8K surface worth of pixels). Exact content revisions
  reuse the target; safe resource-stable direct/opaque multi-batch changes use
  the composition-local executor; device, translucent, parent-sampling, and
  unsafe embedded batches fail closed to full replay. Target
  replacement/eviction/cache-clear/window-destroy shut down the old engine.
  The focused GUI dynamic and multi-window bootstrap runs both reached their
  files but emitted no terminal verdict, so this is source-reviewed mechanism
  only, not an executed self-hosted parity claim.
- Composition damage now preserves multi-batch metadata through the stable
  patch transaction; its bootstrap focused spec passes 6/6. This removes the
  prior classifier-only multi-batch FULL rule, but does not loosen executor
  eligibility for offscreen/device batches.
- The hosted WM now forwards its actual dirty rectangles to the persistent
  Engine2dCompositorBackend. After 20 successful full composition samples on
  that exact engine/viewport, the backend derives a conservative p95 full-width
  row upper bound and asks the shared 256/64/32 scheduler to admit LOCAL work;
  rejected, deferred, FULL, or unsafe batch plans use the existing full path.
  A GPU-selected session records no calibration sample unless backend identity,
  `device_readback`, framebuffer handle, and device identity all agree.
  The focused compositor full→scheduled-LOCAL parity spec passes 8/8 under the
  bootstrap seed. This is CPU/direct mechanism evidence, not a device-present
  or 8K/80 result.

## Acceptance Criteria

- AC-1: CPU Engine2D SIMD spans retain scalar parity, remove redundant copies,
  and have exact x86, ARM64, and RV64 kernel receipts plus native resume steps.
- AC-2: Bare Engine2D fill has one exact-pixel x86/ARM64/RV64 terminal matrix
  receipt; booted scanout remains gated on an admitted Stage-4 CLI.
- AC-3: Vulkan presentation carries presenter-owned physical-adapter and
  Engine2D-buffer ownership receipts and rejects foreign buffers before copy.
- AC-4: DrawIR, Web, GUI, and WM use canonical DrawIR only; NONE/LOCAL/FULL
  schedules fail closed and retain full-replay parity.
- AC-5: The 8K benchmark harness writes exactly one terminal receipt on normal,
  shell-failure, and external process-group termination paths.
- AC-6: No CPU, bare, Vulkan, DrawIR, Web, GUI, or WM 8K/80 row is promoted
  without a fresh 7680x4320 native p95<=12.5ms, RSS, checksum/readback,
  known-completion, no-fallback receipt.
- AC-7: Current plan/report resume matrix links do not rewrite history or
  promote blocked evidence.
- AC-8: Internal optimization/evidence seams and outstanding blockers are
  documented; no user-facing guide or new WebIR/GuiIR is required.

## Latest mechanism update

- The registered SIMD `fill_const`, `SRC_OVER_CONST`, and `SRC_OVER_IMAGE`
  dispatcher slots now use the native in-place span ABIs instead of allocating
  row buffers. Offset/neighbor fill parity, an 8K image-span dispatch parity
  scenario, and source-route contracts were added. The only check available
  this turn was the forbidden bootstrap seed and produced no verdict, so this
  is not speed evidence.
- DrawIR occlusion now has a stable-ID atomic update/remove prerequisite and
  fail-open shape/workspace guards. It remains disabled: no production lowerer
  yet provides complete identities, resource revisions, or exact opaque proofs.

## Scope Exclusions

- Publishing a Rust seed as self-hosted compiler authority.
- Treating llvmpipe or QEMU kernel correctness as physical-GPU or booted 8K
  evidence.
- Rewriting DrawIR producers into WebIR or GuiIR.

## Phase

dev-in-progress

## Evidence Log

- The CPU public SoftwareBackend image/constant blend paths use the public
  in-place span ABI; no row gathering/scattering remains. Structural public
  path coverage exists; seed-run BDD verdicts remain unavailable.
- Exact bare fill matrix passed on x86-64 SSE2 host-user, ARM64 NEON QEMU-user,
  and RV64 RVV QEMU-user. This excludes booted display and 8K claims.
- Native blend bridges now cover bounded x86 SSE2/AVX2, ARM64 NEON, and RVV
  mixed-image/fractional-constant blocks; scalar fallback remains for overlap,
  tails, and unavailable ISA. Direct x86, AArch64 QEMU, and RV64GCV QEMU C
  span-oracle gates pass.
- Native C 7680-row receipt is exact: opaque image 1.171x scalar, opaque
  constant 6.244x, mixed alpha 1.106x. It is not end-to-end 8K/80 evidence.
- Web LOCAL metadata is consumed by the persistent compositor cache and hosted
  entry points. Its focused compositor parity fixture is source-complete but
  blocked before execution by an unrelated bootstrap parser failure; outer WM
  damage translation and partial swapchain present remain separate open gates.
- The Web retained receipt now crosses the child-to-WM boundary: `WmContentFrame`
  carries only execution-owner NONE/LOCAL/FULL damage tied to producer revision
  and accepted resources. The outer compositor rejects overlap/mismatch,
  translates LOCAL rectangles in i64 and clips before narrowing, and retains a
  validated NONE frame as a no-present path; all other states mark the full
  outer surface. Its focused boundary test is blocked before its fixture by the
  same unrelated bootstrap parser failure.
- Hosted Winit now has an additive Vulkan-present bridge: only a fresh
  device-readback candidate with exact non-overlapping LOCAL/canonical FULL
  rectangles, increasing frame revision, stable framebuffer/device/physical
  adapter identity, and a successful pre-acquire ownership receipt reaches
  `present_damage_with_receipt`. All other cases retain the existing
  pure-pixel window fallback. The facade/runtime-hook linkage and a live
  swapchain receipt are not yet verified, so this is G1 mechanism work only.
- The Winit side of the presenter ABI is now real and fail-closed: the sibling
  `spl_winit` cdylib exports matched live-slot Xlib/XCB/Wayland
  platform/display/surface triples and returns zero for invalid slots or
  unsupported families; `vulkan_presenter.spl` resolves those three symbols
  through that same sibling library and closes it after the runtime has copied
  the values. Its focused Rust unit test passes 2/2. These are borrowed raw
  handles, never `VkSurfaceKHR` ownership, and are not a presentation receipt.
- The presenter exports now belong to `vulkan_graphics_runtime::STATE` (the
  Engine2D buffer registry), not the separate Vulkan SFFI registry. The owner
  consumes a validated Winit triple before allocation and implements the
  acquire → device-buffer-copy → fence → present transaction; this is
  compile-checked mechanism work, not a link, runtime, or presentation receipt.
- The canonical runtime foundation now reconstructs only validated Linux raw
  triples, enables the matching instance extensions, creates an owned surface,
  selects a present-capable device, creates a swapchain, and adopts all three
  into `vulkan_graphics_runtime::STATE` before any Engine2D resource exists.
  Its focused invalid-triple test passed 1/1 under `simple-runtime` with the
  Vulkan feature; focused presenter unit coverage is now 3/3 (invalid triples,
  exact-rectangle validation, and failed-acquire poisoning). Typed compiler/interpreter registration and the internal
  ownership/copy/fence/present mechanisms are now present; archive linkage,
  live receipts, and admitted-native evidence remain deliberately unclaimed.
- The same runtime owner now contains the internal acquire/copy/present
  transaction: it verifies the exact device-owned framebuffer, rejects empty,
  out-of-bounds, and overlapping regions, forces a full copy for an unseeded
  or stale acquired image, records per-image revision only after a fence and
  successful present, and otherwise reports partial/full/retained outcomes.
  `cargo check -p simple-runtime --features vulkan --lib` passes after this
  change. It remains internal until typed compiler/native exports can validate
  and pass Simple damage tuples; no live transaction has been claimed.
- G1 now has a typed managed-array ABI boundary: the canonical Simple facade
  passes its `[i64]` tuples as a registered runtime array handle, while Rust
  validates heap type, layout, and integer cells before touching the presenter.
  Native codegen has all presenter signatures and `native_all` has explicit retention
  providers and typed interpreter dispatch registrations. `cargo check -p
  simple-compiler --lib` passes. The separate
  `simple-native-all --features vulkan` check is blocked before those providers
  by the external vendored `rspirv` crate missing `vendor/rspirv/dr/build.rs`;
  no archive or admitted-native claim is made from the codegen check.
- A Sol review closed two fail-closed defects in that mechanism: interpreter
  mode now materializes `[i64]` tuple storage through a typed
  managed-array adapter, and a transaction that fails after acquire
  poisons only that presenter handle instead of allowing a later unbounded
  acquire. Presenter GPU waits now hold only that presenter's mutex, not the
  global runtime registry. The raw-pointer ABI was removed. The public ABI now takes a registered
  RuntimeArray handle and checks type/layout/integer cells before touching
  Vulkan; its focused forged-vs-registered regression passes. It has no
  live/admitted verification receipt.
- After removing the obsolete raw symbol from the runtime export set, compiler
  ABI table, interpreter dispatch, and native retention set, both
  `cargo check -p simple-runtime --features vulkan --lib` and
  `cargo check -p simple-compiler --lib` completed without diagnostics.
- The post-acquire error path now retains the acquire semaphore, source buffer,
  and any command/fence with unknown completion in a poisoned presenter-owned
  quarantine. Destroy keeps that presenter registered until `wait_idle` and
  command recovery succeed; failed recovery keeps ownership intact. Retained
  frames consume acquire through an empty fenced graphics submit, and any
  enqueued WSI present makes destroy retain the swapchain because portable
  Vulkan has no present-completion fence. This is a compile-checked lifetime
  repair, not a live swapchain or 8K receipt.
- O2 now has a stable-ID DrawIR transaction prerequisite: a staged complete
  target order validates revision continuity, duplicate/missing IDs, required
  upserts, and tombstones before publishing; any invalid transaction returns
  the untouched prior command list. The standalone occlusion workspace now
  fails open on lockstep-column/capacity mismatch instead of truncating input.
  A full PaintChunk adapter now wraps producer-supplied IDs and matching
  geometry in one canonical DrawIR composition and derives complete upsert/
  remove transactions. No production PaintChunk producer invokes it yet, and
  visibility culling remains disabled.
- Producer audit confirms this is a real boundary, not a missing call: no live
  Web, GUI, or WM producer currently emits retained PaintChunks together with
  transform/clip/effect-resolved bounds and exact opaque proofs. Post-DrawIR
  reconstruction would be unsound, so production occlusion stays disabled
  pending that producer-owned frame contract.
- Blink now has an additive background-only retained-row producer beside its
  unchanged isolated-frame pixel path. It emits lockstep `PaintChunks`, rects,
  and durable `blink-bg:<node-id>:0` IDs in document order and can lower them
  to the canonical composition adapter. Borders, shadows, glyphs, effects,
  retained execution, and opaque proofs are deliberately still excluded; this
  is a producer foundation, not an enabled culling or performance result.
- Vulkan adopted-presenter device retention prevents Engine2D reselection from
  breaking buffer ownership. Direct present now exposes status, rect count,
  copy bytes, fallback, and no-readback receipt fields; native Winit proof is
  pending.
- Benchmark terminal-receipt supervision and current resume matrix/process
  docs are present; actual Simple 8K rows remain unavailable under the seed.
- Stage 3 linked non-vacuously (815 compiled, zero failed). A Stage-4 candidate
  also linked 815/0, but admission was withheld because compiled roots changed
  while the shared build ran. It was not deployed and native gates remain shut.
- The currently live authority campaign is intentionally Stage-2-only at
  `/mnt/data/bs2/perf-integrated-50a996`; it has no Stage-4 artifact or
  admission receipt. The next authority-owned gate is a stable-snapshot Stage-3
  rerun that exercises the existing bare-leaf `bytes` suffix-resolution repair.
- Git HEAD equals origin/main, but the shared worktree has more than 1,000
  mixed paths; no safe commit/push exists.
- C2 typed forwarding is a deliberately partial mechanism: `HirForwardDecl`
  can reconstruct Phase-2 `alias fn/me` text in unit tests, but production
  parsing discards those declarations. `ParserModule` and `ParserClass` carry
  no forwarding relation or source text, and no HIR/driver pass calls
  `lower_forward_decls`. The next safe compiler slice is parser-owned
  `ParserForwardDecl` capture followed by structured lowering; do not make the
  raw-source scanner a production contract.
- G1 remains mechanism-only after lifecycle review. The Engine2D presenter uses
  `VulkanSwapchain::replacement`, not the unsafe legacy `recreate`. Its typed
  `rt_vk_engine2d_presenter_recreate` route is now re-exported and exposed by
  the Simple facade, but hosted resize/out-of-date routing and a live WSI
  recovery receipt remain open. The old public `rt_vk_swapchain_recreate` is
  fail-closed and the nontransactional `VulkanSwapchain::recreate` method has
  been removed, so no raw recreate escape hatch remains.
- The typed G1 recreate ABI is now threaded through runtime re-export, Simple
  facade, interpreter allow-list, codegen SFFI table, and native-all retention.
  The Vulkan compiler check initially exposed a missing `MirInst::AggregateCopy`
  match in SPIR-V lowering; it now fails closed with a concrete unsupported
  aggregate-storage diagnostic rather than aliasing a value struct, and
  `cargo check --locked --offline -p simple-compiler --features vulkan --lib`
  completes with only existing warnings. This is compiler mechanism evidence,
  not a live WSI or admitted-native result.
- The full Vulkan native retention surface now also compiles:
  `cargo check --locked --offline -p simple-native-all --features vulkan --lib`
  exits 0. That closes the presenter symbol-manifest and retained-function ABI
  linkage check only; it does not provide a native archive, WSI, GPU, or 8K
  receipt.
- The legacy raw `rt_vk_swapchain_recreate` ABI is now retained only as a
  fail-closed compatibility symbol (`NotSupported`); its focused Vulkan runtime
  unit test passes 1/1. It no longer reaches nontransactional
  `VulkanSwapchain::recreate`, leaving presenter-owned `replacement` as the
  sole recovery mechanism. This remains mechanism evidence, not a live WSI
  result.
- A focused high review passes the repaired presenter ABI surface: the retained
  present function is four `i64` arguments at every native boundary, all 14
  presenter symbols are in the generated runtime-symbol manifest, receipt
  exports are scanner-discoverable literal `no_mangle` functions, and the
  additive runtime ABI minor is 1.7. This does not waive the remaining WSI
  lifecycle and live-evidence gates.
- The independent full-bootstrap attempt reached Stage 3 but exited 139 while
  beginning its second streaming parse. Its retained GDB replay identifies
  `ast_gen_harden_enabled` as the faulting function during `ast_reset`. The
  reset-only `SIMPLE_AST_GEN_HARDEN` cache used a module-array slot that became
  invalid across native parses. The gate now reads its environment owner
  directly, the stale slot/refresh path is removed, and the native AST arena
  regression asserts that this reset-sensitive cache cannot return. Static
  hygiene passes; a fresh authority run is required for executable proof.
