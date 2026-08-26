# GPU External Environment Qualification

**Executable source:**
`test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl`

This aggregate answers whether every declared GPU hardware or external-library
dependency works through its production HAL/wrapper. It distinguishes presence,
loadability, emulator semantics, and physical execution.

## Operator flow

1. **Probe backend environment and wrapper ownership.** Confirm the glossary
   contract and identify each external dependency and evidence class.
2. **Upload CPU input through the HAL.** Require retained physical Vulkan and
   CUDA receipts rather than tool/library presence. Vulkan evidence also binds
   the loader hash, validated compiler artifact hash, and production
   `SimpleWebLayout+DrawIR+Engine2D` device readback.
3. **Dispatch offloaded GPU rendering logic.** Require repeated dispatch through
   the production session owner.
4. **Download GPU output through the HAL.** Require exact device-origin bytes or
   pixels, positive stable identity/handle, and no CPU fallback.
5. **Verify communication and rendering parity.** Compare with an independent
   CPU oracle and require invalid-transfer rejection.
6. **Classify physical emulated and blocked evidence.** Metal emulation remains
   `emulator`; native macOS Metal and Windows DirectX remain blocking rows.

## Current environment matrix

| Environment/backend | Classification | Retained evidence |
|---|---|---|
| Linux Vulkan | `physical-device` | HAL/compiler receipts, production PPM, ordered JSONL events |
| Linux CUDA | `physical-device` | upload/dispatch/download receipt; invalid upload/download are both `-1` |
| Metal emulator | `emulator` | exact emulator parity receipt; never promoted to hardware evidence |
| macOS Metal | `blocked` | TODO 652 requires prepared-host native readback |
| Windows DirectX | `blocked` | TODO 653 requires prepared-host native readback |

The Vulkan production receipt names
`production_web_vulkan.ppm` and `production_web_vulkan.events.jsonl`; the
aggregate checks the ordered producer, DrawIR, Engine2D, dispatch, and readback
events. The CUDA receipt must retain `invalid_upload_status=-1` and
`invalid_download_status=-1`.

## Pass boundary

The first four scenarios qualify the available Linux environment. The final
scenario deliberately fails while TODO 652 or TODO 653 is open. Therefore this
manual cannot be used to claim “100% external environment qualification” until
native macOS Metal and Windows DirectX receipts are retained and the blocking
scenario is replaced by assertions over those physical-device receipts.

Run after the focused backend environment tests:

```text
bin/simple test test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl --mode=interpreter --no-session-daemon
```
