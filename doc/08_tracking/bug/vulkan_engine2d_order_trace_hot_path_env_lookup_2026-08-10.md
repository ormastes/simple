# Vulkan Engine2D order tracing taxed every production draw

Status: fixed in source; live Vulkan timing remains part of the admitted CLI gate.

## Defect

The disabled `SIMPLE_VK_ORDER_TRACE` diagnostic path called `env_get` and
constructed interpolated diagnostic text for every Vulkan primitive dispatch,
batch flush, image composite, framebuffer readback, and font-compositor event.
The cost was paid by ordinary Linux and SimpleOS ARM frames even though no trace
line could be emitted.

## Shared-owner fix

`backend_vulkan_helpers.spl` now resolves the process-scoped environment switch
once. Every Vulkan backend and font call site checks that cached boolean before
constructing its message. The diagnostic remains opt-in with identical output
when the variable is set before process startup; disabled frames perform only a
cached branch and retain the existing DrawIR-to-Engine2D ownership path.

The cached value is intentionally immutable. There is no testing override that
can leak a stale enabled state between examples; subprocess tests must set the
environment before startup, matching the production contract.

## Evidence

`test/01_unit/check/vulkan_engine2d_trace_hot_path_contract_spec.spl` pins the
one-time configuration and guarded construction at dispatch, flush, image,
readback, and font sites. Live timing is intentionally not claimed until a
provenance-approved self-hosted binary can run the Vulkan gates.
