# HTML/CSS macOS MoltenVK Portability Probe - 2026-06-18

## Scope

This report records the macOS portability lane from
`doc/03_plan/sys_test/html_css_spec_traceability.md`.

It does not replace the original Linux Chrome/Vulkan RenderDoc completion gate.
Apple platforms expose Metal natively; Vulkan evidence on macOS requires a
portability layer such as MoltenVK, and Chrome's default macOS rendering path is
not the same native Linux Vulkan path.

## Host

Probe time:

- `date_utc=2026-06-18T02:53:51Z`
- `date_local=2026-06-18T11:53:51+0900`

Host facts:

- `macos_version=26.5`
- `macos_build=25F71`
- `uname=Darwin 25.5.0 arm64 arm`
- `architecture=arm64`
- `cpu=Apple M4`
- `gpu=Apple M4`
- `Metal.framework=present`
- `xcrun=/usr/bin/xcrun`
- `xcrun_metal=/var/run/com.apple.security.cryptexd/mnt/com.apple.MobileAsset.MetalToolchain-v17.3.7003.10.RVYeMT/Metal.xctoolchain/usr/bin/metal`

## Vulkan SDK / MoltenVK

Homebrew did not expose a `vulkan-sdk` cask in this environment. The current
package-manager path was installed instead:

```sh
brew install vulkan-tools
```

Installed formulae and versions:

- `vulkan-tools=1.4.350.0`
- `molten-vk=1.4.1`
- `vulkan-loader=1.4.350.0`
- `vulkan-headers=1.4.350.0`
- `glslang=16.3.0`
- `spirv-tools=1.4.350.0`
- `spirv-headers=1.4.350.0`

Installed tool paths:

- `vulkaninfo=/opt/homebrew/bin/vulkaninfo`
- `moltenvk_prefix=/opt/homebrew/opt/molten-vk`
- `vulkan_tools_prefix=/opt/homebrew/opt/vulkan-tools`
- `selected_icd=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`
- `vulkaninfoSDK=missing`
- `vkvia=missing`

MoltenVK verification:

```sh
VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json \
  vulkaninfo --summary
```

Relevant result:

```text
Vulkan Instance Version: 1.4.350
GPU0:
  apiVersion         = 1.4.334
  driverVersion      = 0.2.2209
  vendorID           = 0x106b
  deviceID           = 0x1a040209
  deviceType         = PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU
  deviceName         = Apple M4
  driverID           = DRIVER_ID_MOLTENVK
  driverName         = MoltenVK
  driverInfo         = 1.4.1
  conformanceVersion = 1.4.4.0
```

Result: Vulkan-over-Metal portability is available through MoltenVK on this
host.

## RenderDoc

The canonical helper did not discover a RenderDoc CLI:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/macos-portability-2026-06-18 \
  sh scripts/tool/renderdoc-evidence.shs env
```

Result:

```text
rdoc_root=/Users/ormastes/simple
rdoc_home=
rdoc_cmd=
rdoc_lib=
rdoc_chrome=
rdoc_output_dir=build/renderdoc/macos-portability-2026-06-18
rdoc_timeout_secs=45
```

The setup wrapper also reported:

```text
rdoc_status=missing-renderdoc
setup_exit=1
```

The canonical capture commands were intentionally run without adding ad hoc
macOS command variants:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/macos-portability-2026-06-18 \
  sh scripts/tool/renderdoc-evidence.shs capture-simple

RDOC_OUTPUT_DIR=build/renderdoc/macos-portability-2026-06-18 \
  sh scripts/tool/renderdoc-evidence.shs capture-html
```

Both commands returned:

```text
SKIP: renderdoccmd not found under build/tools/renderdoc*
```

No `.rdc` file or evidence directory was produced under
`build/renderdoc/macos-portability-2026-06-18`.

## Browser Path

Google Chrome is installed as a macOS app:

- `/Applications/Google Chrome.app/Contents/MacOS/Google Chrome`
- `Google Chrome 149.0.7827.116`

The canonical helper did not discover this executable because its browser
lookup is currently scoped to Linux Chrome/Chromium paths. Since no RenderDoc
CLI was available, the browser path was not captured and could not be
classified as Vulkan-over-Metal, direct Metal, or unavailable-by-runtime.

Result: browser RenderDoc evidence is unavailable on this macOS host. The
concrete blocker is missing `renderdoccmd`.

## Evidence Status

| Evidence item | Status | Detail |
| --- | --- | --- |
| macOS host facts | recorded | macOS 26.5 / arm64 / Apple M4 / Metal present |
| Vulkan SDK or MoltenVK device | pass | Homebrew `vulkan-tools=1.4.350.0` and `molten-vk=1.4.1`; `vulkaninfo` reports Apple M4 with `DRIVER_ID_MOLTENVK` |
| RenderDoc CLI | unavailable | canonical setup reports `rdoc_status=missing-renderdoc` |
| Simple Vulkan RenderDoc capture | skipped | `capture-simple` skipped before capture because `renderdoccmd` is missing |
| Chrome HTML/CSS RenderDoc capture | skipped | `capture-html` skipped before capture because `renderdoccmd` is missing |
| `.rdc` artifact | absent | no file produced under `build/renderdoc/macos-portability-2026-06-18` |

## Conclusion

The macOS portability restart path is complete for this host as supplemental
evidence: Metal is available and MoltenVK exposes an Apple M4 Vulkan portability
device, but RenderDoc CLI is not installed or discoverable, so no macOS `.rdc`
capture can be produced.

This report is supplemental portability evidence only. The original completion
gate for Chrome HTML/CSS RenderDoc evidence still requires an external host
where Chrome-on-Vulkan can be captured and validated by
`scripts/check/check-renderdoc-html-external-host-gate.shs`.
