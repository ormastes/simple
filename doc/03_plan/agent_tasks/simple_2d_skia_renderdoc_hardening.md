<!-- codex-design -->
# Hardening task ownership

Coordination: parent Codex owns integration and final review. This document owns proposal names before additional sidecar implementation. Lower-model sidecars: N/A; no lower-model findings accepted without parent review.

| Lane | Owns | Must not change independently |
|---|---|---|
| Research/design | These feature-scoped docs and knowledge receipt | Existing accepted requirements/dirty registry |
| 2D bridge | `src/lib/skia/bridge/engine2d_bridge.spl` and focused bridge regressions | Shared DrawIR schema or native ABI |
| Shared IR, pending selection | Existing common DrawIR types, serializers and migration | Web-specific duplicate IR |
| Web | Existing browser_engine producer, corpus imports and source metadata | Backend operation semantics or capture verdict |
| GUI | Widget/direct-2D scene production and visible-state evidence | Private raster contract |
| Capture | renderdoc_diff parser/alignment and exporter regression evidence | Upstream provider or renderer implementation |
| Upstream provider, pending selection | Optional pinned native adapter and SFFI lifetime | Public Skia API replacement or default linkage |

Shared API/receipt/helper names are specified in the architecture and detail design. Lane owners coordinate signature changes before edits. Every unfinished executable helper fails explicitly; no TODO pass. Shared IR is one owner's responsibility. Parent reconciles source/ZIP discrepancies and verifies each criterion once, maximum three fix/verify cycles. Native GPU evidence remains blocked until a real admitted host exists; no synthetic row substitutes.

Merge order: bounded bridge/capture repairs → parent review → user choice of broader scopes → shared contract migration → optional provider → Web/GUI corpus → native evidence. Existing unrelated dirty files are excluded from this lane and any commit.

## Case 02 affine implementation order

| Lane | Owner/interface | Gate before merge |
|---|---|---|
| Shared v4 | One shared-IR owner: `DrawIrAffine2D`, raster policy, SDN and UiIr | V3 compatibility; invalid matrix rejects atomically; every legacy consumer refuses v4 |
| Web source | Browser producer owner: CSS transform order/origin, full painted `#scene` inventory, surface clip and source indexes | Real pinned case 02 produces all commands or one explicit whole-scene rejection |
| Engine2D Vulkan | Strict GPU owner: affine coverage pipeline and completed readback | No host transform fallback; interior/exterior, edge and diagonal-seam oracle gates |
| Skia provider | Optional-provider owner: private v3 payload and pinned Ganesh implementation | V1/V2 ABI unchanged; full preflight and resource lifetime; native build |
| Independent pixels | Evidence owner: polygon coverage oracle, color domain, manifest threshold, capture receipts | Threshold pinned before device output; physical UUID, completion and final-target proof |
| GUI integration | GUI owner: same v4 transform semantics where widgets request them | Visible-state and input scenes retain source mapping; no duplicate raster IR |

Parent Codex is merge owner; Astra is final read-only architecture reviewer.
The shared v4 transport, UiIr lowering, and audited legacy rejection paths
are implemented and statically reviewed; their runtime gate is still open.
The Web and Vulkan affine paths, independent pixel oracle, case 02 capture
adapters and runner commands now have source candidates but no trusted runtime
or physical result. Skia private-v3 native drawing is behind a default-off
build flag; submitted-matrix provenance and a pinned-header build remain open.
GUI input has a pinned event-to-DrawIR scene but no native text wire, font
pin, independent pixel oracle or physical runner route. Astra reviewed that
boundary: use the existing shared text command, qualify Engine2D's strict
text path, and define a separate bounded native glyph format before runner
integration. Parent remains merge owner and final reviewer. No release work
begins before a trustworthy verify PASS.

## Current worktree checkpoint (2026-09-26)

The bounded lanes have source changes in this worktree: strict Skia-to-Engine2D
preflight/readback receipts, fail-closed v1 RenderDoc event validation, exporter
cleanup, a pinned 48-case web corpus, and truthful GUI pairwise evidence. The
RenderDoc exporter offline contract suite passed 21 mock tests. The corpus byte
audit matched 48 cases, eight references and one SVG. Working and staged
direct-env-runtime guards passed; the scoped diff has no whitespace errors.

Simple specs and native rendering are **not verified**. The available release
binary fails while parsing clean `src/lib/nogc_sync_mut/io/process_ops.spl`, and
another release binary exited 139 during test setup. The checkout's `bin/simple`
is a Rust bootstrap seed, not the required self-hosted runtime. No native
RenderDoc replay or Skia Vulkan build was performed on this macOS host. The
imported corpus retains `not-run` rendering status and no screenshot baseline
was admitted.

An isolated test-runner native-build attempt used its own cache/output path and
`SIMPLE_NO_STUB_FALLBACK=1`. It stopped at `SCV-E-ADMISSION:
filesystem-event-journal-missing` before producing objects. SCV admission uses
the checkout's shared `build/scv` and `.scv` paths even when native-build's
object cache is isolated. Do not clear those shared paths while other sessions
may own them. The next verifier attempt needs an isolated source checkout with
its own SCV journals, or an admitted current self-hosted binary from its owner.

An isolated local checkout now exists at
`/private/tmp/simple_2d_verifier_20260926`, with only this rendering lane's
tracked diff and imported corpus applied. The earlier cold-init attempt is
terminal. A later attempt selected the clone's Windows PE worker on macOS and
exited 126. The final bounded attempt explicitly selected an absolute Mach-O
bootstrap worker and reached linking, but `core-c-bootstrap` lacked Vulkan and
CUDA runtime symbols. It exited 1 without producing a verifier executable.
The terminal log and exit receipt are under `build/mini_builds/` in that
clone. The three-cycle cap is reached; do not restart the verifier build in
this session.

The user selected feature C and evidence N2 on 2026-09-26. Final requirements
are in `doc/02_requirements/{feature,nfr}/simple_2d_skia_renderdoc_hardening.md`;
the unselected option files were removed. Active parallel owners now cover
versioned fractional DrawIR, canonical final pixels, optional upstream Skia
Ganesh Vulkan, and Web/GUI corpus integration. The parent owns final API
integration and review; Astra owns read-only design review.

Next: fix the native test-runner closure/lane mismatch in a fresh scoped
session, restore a current self-hosted verifier, and first run a false-matcher
negative control. Then run focused bridge, parser, Web and GUI specs once and
qualify native capture on an admitted physical Linux Vulkan device. Keep the
goal open until those requirements are evidenced.

Before registering more corpus scenes in the physical runner, split its
growing `main.spl` into scene descriptors, worker/capture, and receipt
verification modules with one owner for each interface. The case 01/06
branches already demonstrate that per-case conditionals do not scale to 48
rows; the capability matrix in `doc/03_plan/sys_test/` groups the reusable
operation families and remaining gates.

The Web producer now retains raw `transform`, `translate`, `scale`, and
`rotate` declarations in computed Style and source DrawIR. Existing
rectangle-only admission requires each to be `none`. The real-producer spec
checks each property and missing-key gate independently, but is unexecuted
under the verifier cap. The decimal box guard now captures authored geometry
tokens in both declaration paths, scans all computed styles before culling,
and blocks rectangle admission for unresolved lengths. Its focused spec is
unexecuted. After the bounded f64 leaf mode below, next implementation must
add typed affine semantics and matching dual-backend coverage before admitting
case 02 or other transform rows.

A separate fractional Web producer mode now resolves tightly bounded opaque
absolute leaves from authored decimal CSS before integer culling and emits
DrawIR v3 f64 rectangles. Unsupported paint, external CSS, pseudo-elements,
scrolling and animation reject the whole scene with zero batches. The focused
spec and manual exist but have no runtime PASS under the verifier cap. The
mode is not yet connected to a complete case 02 GPU/CPU comparison.

## Selected-scope progress (2026-09-26)

The additive DrawIR v3 fractional payload, v2 SDN promotion and integer-only
consumer rejection are implemented. The `aarch64-apple-darwin` runner reported
2/2 on its focused spec. The new `draw_ir_to_ui_ir` lowerer preserves f64
rectangle geometry and rejects unsupported commands atomically; the same
runner reported 8/8 on its focused spec. Those results are provisional because
a negative-control run through this binary stopped at unrelated
`process_ops.spl` parsing before it could prove assertion execution. The older
`bin/release/macos-arm64/simple` is demonstrably vacuous: it reported PASS for
`expect(1).to_equal(2)`. Its reported provider 5/5, pixel 5/5 and system 1/1
were withdrawn as invalid evidence. Broader DrawIR tests hit the unrelated
`sfnt.spl` parser incompatibility or pre-existing spec failures. The additive
`final_output_pixels` API validates completed resource metadata and canonical
RGBA, but its focused test cannot yet run through the current parser path.

The 48-case Web producer and GUI input/visible-command specs exist with
explicitly blocked device receipts. A pinned 16 × 16 Web box, the real corpus
`01-solid-boxes` and `06-rectangular-clip` pages, and two GUI button states now have source-bound
admission, independent pixel oracles, and candidate physical-runner paths.
None has a trustworthy Simple spec PASS or completed physical capture.
The isolated macOS bootstrap attempt terminated after selecting a Windows
PE `bin/simple.exe` as its worker; the diagnosis and safe retry condition are
in `doc/08_tracking/bug/macos_arm64_stale_test_runner_false_green_2026-09-26.md`.
A genuine Linux physical Vulkan host is not accessible in this session;
NFR-2D-002 and dual-backend pixel qualification remain open.

Further C/N2 integration work added a v3 host-queue admission path, a strict
fractional Vulkan primitive raster rule, a controlled-rectangle physical
qualification contract, and a direct Skia-picture-to-DrawIR producer lane.
The controlled contract now has owner-bound dual-backend capture adapters,
but no physical run; manual claims of device type/authentication cannot
satisfy N2. The optional native provider's global lock is no longer held
through GPU work, but its
synchronous submit has no enforceable 5-second bound and native compilation
remains unavailable. The provider currently supports bounded rectangles and
rectangular clips; Web/GUI dual-backend corpus qualification remains a separate,
substantial implementation and device-evidence task.

Both controlled-frame backend paths now have code-owned conversions into
`FinalOutputCapture`: Skia validates its native byte checksum; Engine2D links
the completed fence generation, framebuffer and readback, then validates its
packed-word checksum before RGBA conversion. The pinned controlled fixture
declares its color domain. These conversions still accept constructible data
values and do not authenticate the physical Linux device, driver, or capture
process. The physical comparison remains a candidate until that native
provenance exists. The isolated self-hosted runner build failed at native
linking, so new Simple specs are not verified.

## Next provenance implementation lanes (Astra reviewed)

- Native Skia owner: query Vulkan 1.1 device/driver UUIDs on the selected
  `VkPhysicalDevice`; expose a versioned optional identity export scoped to a
  live, waited, readback-ready completion.
- Host loader owner: resolve that symbol only from the authenticated provider;
  pin the module/session and require the completion authority predicate before
  returning a fixed-size identity record. Keep the existing ABI-v1 table and
  legacy provider loading compatible.
- Engine2D native/SFFI owner: query the selected real device behind the
  completed fence generation. Do not use `VulkanSession.physical_device`
  (placeholder) or compare its opaque logical handle to Skia's index.
- Merge owner: bind both native records to their `FinalOutputCapture`, compare
  canonical lowercase UUID encodings, and keep `candidate` until independent
  session/capture provenance is verified on physical Linux Vulkan hardware.
- Final reviewer: Astra; reject missing extension, stale handles, wrong
  session/completion, software Vulkan, same-name different-UUID cards, and
  post-retirement queries. No UUID test can stand in for a device run.

## C/N2 provenance and Web checkpoint

The optional Skia provider now exposes a versioned device identity record
after owned terminal completion and observed readback. The Simple frame copies
that record before releasing its owner. The Engine2D native owner now returns
a monotonic selected-device generation token and requires the expected token
when querying UUIDs under the same Vulkan state lock; its strict capture path
passes the completed submission token. Astra reviewed the token linkage and
found no further concrete defect. A deployed self-hosted symbol check and
physical Linux dual-backend capture remain open.

The Web element-scroll producer applies case 41's requested offset and records
the resolved ID/offset. Its extent excludes border chrome, and it rejects
viewport-fixed descendants explicitly. Focused source scenarios cover both
edge cases, but no trusted Simple scenario has executed yet. The isolated
verifier attempt is terminal at the three-cycle cap.
