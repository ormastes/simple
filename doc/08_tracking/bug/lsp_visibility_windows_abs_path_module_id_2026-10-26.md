# lsp_visibility derives module and feature ids from the absolute Windows path

Found 2026-10-26 while writing the feature x layer matrix specs.

Symptom: `query_visibility visibility <abs target> --requester <abs requester>` on Windows
returns `layerModule` / `feature` / `module` ids such as
`C:.dev.wt-mdsoc.test.fixtures.mdsoc_matrix.feature_a`. With repo-relative paths the same
call returns `test.fixtures.mdsoc_matrix.feature_a`.

Cause: `relative_to_src` (`src/app/cli/_QueryVisibility/symbol_resolution.spl:327`) strips
only at a `/src/` marker or a leading `src/`. Paths with neither (any fixture or test tree,
any drive-letter path without `/src/`) fall through unchanged, and `.replace("/", ".")` then
keeps the drive prefix. Ids differ per checkout location, so they are not stable keys.

Affected: `boundary_module`, `feature_id_of`, `layer_visible_reason` and the JSON fields built from them.

Fix direction: normalise to a repo-root-relative path (strip the workspace root) before building ids;
keep `/src/` stripping for source files.

Evidence: `test/01_unit/app/lsp/lsp_feature_layer_matrix_spec.spl` passes relative paths and
asserts the exact `feature` id; an absolute-path call is the repro above (seed bin/simple.exe).
No spec covers the absolute-path form yet.

## Resolution (2026-10-27)

`relative_to_src` (`src/app/cli/_QueryVisibility/symbol_resolution.spl`) now first calls the new
`repo_relative_path`: it normalises `\` to `/` and strips the process-cwd prefix (the repo root when run
from it), then applies the existing `/src/` and leading `src/` stripping unchanged. All id builders
(`feature_id_of`, `boundary_module`, `layer_dir_name`, `peer_path_tail`, reason strings) go through it.
Limit: an absolute path outside the cwd is left as is (no `.git` ancestor walk).

Coverage: new `it` in `test/01_unit/app/lsp/lsp_feature_layer_matrix_spec.spl` (REQ-LSP-MATRIX-002) passes
cwd-built absolute paths and asserts `test.fixtures.mdsoc_matrix.feature_a`. Before: 6/7 (new case failed);
after: 7/7. Reruns: feature_layer_matrix 16/16, query_visibility_feature 11/11, lsp_visibility_support 45/45.
