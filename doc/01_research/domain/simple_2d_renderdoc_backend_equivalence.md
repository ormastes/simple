<!-- codex-research -->
# Simple 2D RenderDoc Backend Equivalence — Domain Research

Backend equivalence needs two distinct proofs: detailed command/pipeline/resource equivalence and independently read back pixels against an absolute oracle. RenderDoc capture presence alone proves neither. Linux can provide real Vulkan and software-Vulkan checkpoints; native Direct3D and Metal remain platform-specific.

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence.domain -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence.domain hash=sha256:auto render=ascii
@layout dag
@direction LR

RenderDocReplay -> ActionsPipelineResources
DXVK -> Vulkan
Vkd3dProton -> Vulkan
Lavapipe -> Vulkan
MoltenVK -> Metal
ActionsPipelineResources -> DetailedRecord
Vulkan -> DetailedRecord
Metal -> DetailedRecord
DetailedRecord -> IndependentPixelOracle
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence.domain hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Authoritative Prior Art

| Source | Relevant constraint |
|---|---|
| [RenderDoc](https://github.com/baldurk/renderdoc) | Capture/replay exposes API events and pipeline/resource state; a valid capture must be opened and inspected, not recognized only by file magic. |
| [DXVK](https://github.com/doitsujin/DXVK) | D3D8–11 translation targets Vulkan and is normally used with Wine; installed libraries alone do not prove a submitted D3D frame. |
| [vkd3d-proton](https://github.com/HansKristian-Work/vkd3d-proton) | D3D12 translation targets Vulkan; translated evidence must be labeled separately from native Windows D3D12. |
| [Mesa software rasterizers](https://docs.mesa3d.org/sourcetree.html) | Lavapipe/llvmpipe provides a useful software-Vulkan execution checkpoint with explicit software-device provenance. |
| [MoltenVK](https://github.com/KhronosGroup/MoltenVK) | Vulkan maps onto Apple Metal platforms; it is not a Linux Metal emulator and cannot prove native Metal rendering on Linux. |
| [Apple Metal](https://developer.apple.com/metal/) | Native Metal completion/readback evidence requires an Apple platform and Metal command submission. |

## Derived Domain Rules

- Normalize only documented nondeterministic identifiers/timestamps; never normalize backend, adapter, API, shader/resource identity, dimensions, format, command order, barriers, completion, or readback origin.
- A translated lane records both guest/requested API and actual host API. `DirectX→Vulkan` and `Metal-request→Vulkan` are useful compatibility checks, not native DirectX/Metal proof.
- Require replay-open success, API/device identity, at least one relevant action, resource/pipeline inspection, and an independently produced exact pixel oracle before equivalence passes.
- Preserve native Windows D3D and macOS Metal as fail-closed external checkpoints; Linux absence is an availability result, never an unconditional test pass.

