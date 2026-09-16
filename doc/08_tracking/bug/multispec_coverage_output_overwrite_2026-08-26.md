# Multi-spec coverage output is overwritten by child processes

When `simple test` receives several spec files with one
`SIMPLE_COVERAGE_OUTPUT`, each child writes that same path. The final artifact
contains only the last spec rather than a union of decisions. A five-spec
Engine3D command therefore ended with the pipeline spec's 0/1 decision result
despite earlier font/drawing/geometry/texture execution.

Required fix: derive a collision-free artifact per child and merge only after
checking schema, source revision, runtime/backend identity, static denominator,
and duplicate decision consistency. Until then, multi-spec CSV output is not
admissible aggregate coverage evidence.
