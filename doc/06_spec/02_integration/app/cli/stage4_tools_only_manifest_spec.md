# Stage 4 tools-only wrapper integration specification

> Fail-closed source-level integration coverage for the preparatory Stage 4
> wrapper. It is not evidence of live migration admission.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 2 | 2 | 0 | 0 |

Source: `test/02_integration/app/cli/stage4_tools_only_manifest_spec.spl`

## Scenarios

### Should bind admitted Stage 3 and publish atomically

Inspect the wrapper for the Stage 3 admission receipt, canonical tool journal,
zero-compiler-source counter, atomic publication, and built-tool help/version
smokes.

### Should reject unsafe sources and paths

Inspect the wrapper for contained cache/publication identities, compiler-tree
rejection, and duplicate source/object rejection.

This manual is hand-maintained while the production SPipe/docgen runner is
gated; regenerate it from the executable SSpec after admitted deployment.
