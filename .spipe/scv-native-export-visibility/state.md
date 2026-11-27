# SCV exported native declarations

Stage: verification and review.

Scope: ten existing exported scalar declarations in four library modules gain
`pub`; values and exported names are unchanged. The internal arena maximum
remains private. This resolves the recovered producer's unsupported private
static accessor path for intended public APIs.

Evidence: paired private/public native fixtures reproduce the compile failure
and successful imported-value execution. Real SCV bounds compilation now
passes, and the expanded instrumented probe passed below/above-bound assertions.
The earlier smaller probe discrepancy remains unexplained. See
`doc/08_tracking/bug/scv_exported_static_native_visibility_2026_10_29.md`.

No production BuildRunner manager image or strict Darwin qualification is
claimed. Final full-manager attempt is reserved until known prerequisites
are reviewed. Hosted seed tests are diagnostic only.
