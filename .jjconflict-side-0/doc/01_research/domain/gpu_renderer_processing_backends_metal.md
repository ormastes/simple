<!-- codex-research -->
# Metal MSL Processing Backend — Domain Research

Apple's Metal compute model maps a compute kernel over a grid of threads and
uses buffers for inputs and outputs.  Apple's reference calculation sample also
reads the GPU output and compares it with a CPU calculation, matching this
lane's device-readback/oracle contract:
https://developer.apple.com/documentation/metal/performing-calculations-on-a-gpu

Metal buffer indices are part of the shader/host ABI.  The generated MSL must
therefore freeze output at buffer 0 and parameters at buffer 2 to match the
repository's `metal_sffi_run_compute_frame` interface.  Bounds checking against
the logical element count is required because dispatch grids are rounded to a
threadgroup multiple.

Apple supports both runtime source compilation and command-line precompilation
to a Metal library.  Native evidence should compile the exact retained source
with `xcrun -sdk macosx metal`, link it with `metallib`, and separately exercise
the runtime SFFI path:
https://developer.apple.com/documentation/metal/building-a-shader-library-by-precompiling-source-files

Deterministic source and a semantic cache key are host-independent properties;
successful MSL compilation, pipeline creation, submission, and device-origin
readback require a prepared macOS Metal host.
