<!-- codex-research -->
# Domain evidence: Skia and capture correctness

Researched 2026-09-26 using primary-source search results; no native execution implied.

- [Skia Vulkan integration](https://skia.org/docs/user/special/vulkan/) describes client-owned device/queue supplied through VulkanBackendContext. An optional provider should consume the existing native GPU owner and expose opaque validated handles.
- [GrDirectContext API](https://api.skia.org/classGrDirectContext.html) distinguishes flushing recorded work from submitting it to the GPU. Completion/readback evidence must follow actual submission and synchronization.
- [ANGLE debugging guidance](https://chromium.googlesource.com/angle/angle/%2Bshow/HEAD/doc/DebuggingTips.md) documents RenderDoc interception issues. Backend launch flags need corroboration from the captured process and replay API.

Design inference: preserve native-Skia Vulkan and GL-through-ANGLE Vulkan as distinct provenance routes. Use canonical decoded final pixels and explicit color/alpha/extent metadata for visual equivalence; retain command differences as diagnostics. This follows the ZIP's evidence contract and must still be implemented and tested locally.

The input corpus's software Chromium renders are fixture-authoring evidence only. Navigation, external resource loading, font completeness and Vulkan golden admission require separate checks. No performance targets are introduced by this correctness study.

2026-09-26 follow-up: [Khronos `VkPhysicalDeviceIDProperties`](https://docs.vulkan.org/refpages/latest/refpages/source/VkPhysicalDeviceIDProperties.html)
defines 16-byte `deviceUUID` and `driverUUID` values for correlating devices
and drivers across instances and processes. This is the appropriate pair key
for the separate Engine2D and Skia provider runs. Their current numeric
`device_identity` fields have different meanings (Engine2D's device-present
sentinel `1` versus Skia's enumeration index), so comparing those numbers
would reject valid pairs and
would not establish physical identity. The offline pair contract now checks
reported UUID shape and equality; a trusted backend-owned query and capture
binding remain necessary before a physical PASS can be issued.

2026-09-26 device-loss follow-up: The [Vulkan device and queue specification](https://docs.vulkan.org/spec/latest/chapters/devsandqueues.html) permits cleanup after device loss and treats `VK_ERROR_DEVICE_LOST` as sufficient completion evidence for resources previously in use. The [device destruction reference](https://docs.vulkan.org/refpages/latest/refpages/source/vkDestroyDevice.html) requires child objects to be destroyed before the device. [Skia `GrDirectContext`](https://api.skia.org/classGrDirectContext.html) requires `releaseResourcesAndAbandonContext()` while the Vulkan device and queue remain valid, including after device loss. Design inference: once the provider has retired its child resources, `session_close` may accept `VK_ERROR_DEVICE_LOST` from the idle wait, abandon Ganesh, then destroy the device and instance. Other idle errors remain failures. This source reasoning does not establish a physical device-loss test PASS.

2026-09-26 clip follow-up: [Skia `SkCanvas`](https://api.skia.org/classSkCanvas.html) documents `clipRect(rect, SkClipOp::kIntersect, false)` as an aliased intersection and requires balanced `save()`/`restore()` state. Design inference: one validated rectangular clip can be scoped to one native draw without changing subsequent commands. This does not establish cross-backend pixel parity; a clipped primitive oracle and physical captures remain required.

2026-09-26 affine follow-up: [CSS Transforms Level 1](https://www.w3.org/TR/css-transforms-1/) defines the transform matrix as origin translation, post-multiplication of authored transform functions in order, then inverse origin translation. For `translate(.25px,.25px) rotate(7deg)`, the rightmost rotation acts first on local points. Positive rotation uses the CSS screen coordinate convention. [Skia `SkCanvas`](https://api.skia.org/classSkCanvas.html) exposes matrix concatenation and clipping, while [SkPaint](https://api.skia.org/classSkPaint.html) exposes an antialias request; that request alone does not prove identical edge pixels across renderers. Design inference: resolve CSS order and origin in Web, transport a typed affine matrix, apply surface clip before Skia matrix concatenation, and declare a separate coverage/compositing comparison policy. The current Engine2D strict Vulkan rectangle shader accepts integer bounds and cannot satisfy this case without a new GPU path; the provider's v1/v2 records have no affine coefficients.
