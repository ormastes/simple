<!-- codex-design -->
# Metal MSL Processing Backend Architecture

`ProcessingIr` remains the sole semantic input.  The shared backend pipeline
selects `ProcessingBackendTarget::MetalMsl` and calls a tree-private Metal
generator.  The generator validates IR, emits canonical MSL, binding metadata,
entry point, and semantic key into `ProcessingBackendArtifact`.  Runtime Metal
execution consumes only a successful artifact and returns
`ProcessingCompileEvidence` and `ProcessingDeviceReadbackEvidence`.

The generator owns no Metal handles and performs no I/O.  The existing Metal
SFFI owner retains device, queue, library, pipeline, buffer, submission, wait,
download, and cleanup lifecycles.  CPU execution remains an independent oracle
or explicit fallback and cannot establish GPU provenance.

Startup probes host capability once.  The hot path validates IR, derives the
semantic key, uses an artifact/library cache, binds buffers, dispatches, waits,
and reads back.  Cache identity includes ProcessingIR semantics, target, entry
point, ABI version, and generator version.  Changes to any component invalidate
the entry.  Backend order is Vulkan, CUDA, Metal where supported, then explicit
CPU fallback; platform capability may filter candidates but never relabel a
fallback as GPU work.

Failures are typed and fail closed.  Invalid IR produces no source.  MSL
compiler, pipeline, device, submit, and readback failures have zero handle,
identity, and GPU-completed status.  Native Metal execution is blocked on Linux.

Drawing access is a Metal-to-Metal feature transform below the renderer API.
It retains resource binding numbers, two-dimensional grid coordinates, packed
pixel values, and row-major addressing.  Translation accepts only semantics it
can preserve exactly; unknown or out-of-bounds operations produce an invalid
artifact with no target source.

Budgets: host-independent generation under 10 ms/8 MiB; warm artifact lookup
under 1 ms; native compile, dispatch latency, and max RSS recorded separately on
the prepared macOS host.
