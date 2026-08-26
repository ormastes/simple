# GPU Dynamic Backend and Full Offload Architecture

## Boundary

Application, Web, GUI, WM, and DB code depend on ProcessingIR,
DrawIrComposition, Engine2D, or the web/DB batch facade. Platform GPU libraries
are optional providers below those owners. They never own WebIR, Draw IR,
network protocol state, transaction durability, or presentation policy.

## Hosted provider capsule

`runtime_dynload.c` owns host library open/symbol/close and three independent
provider slots: CUDA, Vulkan, and Metal. Each slot binds a configured path to
ABI version, backend capability bits, a complete required-symbol surface, and
one local library handle. Admission is fail-closed and atomic from callers'
perspective. Registry lookup is serialized; operation execution is not run
under the registry lock.

Core-only builds retain weak unavailable probes in `runtime_native.c`. Builds
that include the dynamic-loader owner define `SIMPLE_RUNTIME_DYNLOAD_OWNER`,
which removes those fallback definitions so COFF/MSVC and ELF/Mach-O products
have one owner.

## Lifecycle

The current safe replacement contract is process-bound or explicitly quiesced:
load, create sessions/resources, submit and complete work, destroy resources,
unload, change the configured provider, then load again. Unloading live objects
is invalid. Future in-process hot replacement must add provider/session
refcounts and a quiescence receipt before expanding this contract.

## Evidence ladder

Provider admission is only the first rung. A backend claim requires artifact
validation, submission, fence/completion, device-origin readback, stable device
identity, and exact CPU-oracle parity. Rendering and web/DB profiles additionally
separate producer/IR construction, marshaling, submit, device, synchronization,
readback, and end-to-end time.

