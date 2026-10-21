# Web transform provenance and rectangle admission

Manual companion to
`test/03_system/app/ui/feature/web_transform_provenance_spec.spl`.
Generated SPipe output awaits a trustworthy Simple runner.

The real Web producer renders two nodes sharing authored `transform`,
`translate`, `scale`, and `rotate` declarations, plus an untransformed child.
The scenario checks that both computed node styles and both source DrawIR
commands retain all four raw values after cascade and layout reconstruction.
The child retains `none` defaults. Four geometry-normalized probes isolate
each non-neutral property and require its exact rejection key. Four more
probes omit one required key at a time and require its exact missing-key
rejection.

Requirement: REQ-2D-006. This checks provenance and fail-closed admission;
it provides no fractional, affine, pixel, or physical Vulkan verdict.
