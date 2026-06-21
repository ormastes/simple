# UI and GUI Feature Expert

## Role

Maintain feature-specific process knowledge for UI and GUI. Use this skill when work touches this feature area and keep it current as the project process produces new artifacts.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Feature Links

- [GUI architecture](../../../04_architecture/compiler/graphics/gui_layer_contract.md)
- [Drawing stack](../../../04_architecture/ui/drawing_stack.md)
- [Graphical icon system](../../../04_architecture/ui/graphics/graphical_icon_system.md)
- [GUI/web/2D Vulkan RenderDoc capture guide](../../../07_guide/tooling/renderdoc_capture_infra.md)
- [Vulkan-backed 2D rendering guide](../../../07_guide/ui/gpu_backends/vulkan_backed_rendering.md)
- [Web render backend guide](../../../07_guide/ui/web_render_backend.md)
- [App source](../../../src/app/)

## GUI/Web/2D Vulkan RenderDoc Verification

Current canonical setup is macOS-first. Before claiming GUI/web/2D Vulkan
parity, run the macOS host probe and compare all three lanes from the same
fixture:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

Required lanes:

- Electron Chromium with requested `--enable-features=Vulkan --use-angle=vulkan`.
- Original Chrome with the same Vulkan/ANGLE request.
- Pure-Simple GUI/web/2D through Engine2D Vulkan readback.
- RenderDoc `.rdc` evidence with `RDOC` magic for each capture lane.

On macOS, Vulkan readiness means `vulkaninfo --summary` reports MoltenVK, not
that Chrome/Electron accepted ANGLE Vulkan and not that RenderDoc is installed.
Homebrew covers the Vulkan/MoltenVK stack, but the macOS runbook must record
`gui_web_2d_vulkan_renderdoc_macos_homebrew_package_status` because this host
has no `renderdoc` formula or cask. Upstream official RenderDoc support lists
Windows/Linux/Android rather than macOS; use only a project-approved
`RenderDoc.app`/fork or unpacked tree that actually contains `renderdoccmd`.
If Electron or Chrome renders pixels but records `vulkan-angle-unavailable`,
keep the browser Vulkan gate failed and compare only as fallback bitmap
evidence. If `renderdoccmd` is unavailable, the setup scripts expose
`rdoc_status_reason`, `gui_web_2d_vulkan_renderdoc_reason`, package/support
status, and install hints; do not treat missing RenderDoc as a skipped pass.
Windows and Linux capture gates should be added later with the same evidence
keys.

## Update Rule

After research, requirements, architecture, design, implementation, verification, or release work changes this feature area, add or refresh links here so the next agent can start from the current project state.

Template: [feature_skill.md](../../template/feature_skill.md)
