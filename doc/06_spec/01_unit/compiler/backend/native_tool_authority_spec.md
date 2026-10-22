# Strict native tool authority

Source: [native_tool_authority_spec.spl](../../../../../test/01_unit/compiler/backend/native_tool_authority_spec.spl).

Status: authored manual; all runtime scenarios **UNRUN** for this change.
This manual was maintained from the executable spec. Docgen was not executed.
The spec uses the existing SSpec runner and production authority APIs.

## Canonical linker target

### REQ-MOLD-001 — Decode a complete projection whose ld resolves to mold

1. Start with all eight required tool roles and six environment assignments.
2. Replace the linker row with the canonical `/usr/local/bin/mold` path and
   digest observed in the r16b tool manifest.
3. Decode through `native_tool_projection_decode_v1`.
4. Require eight pins, exact linker role/path/digest, and unchanged `cc` and
   `llc` role/path pairs.

This checks projection parsing. Fixture digests do not constitute file
admission, execution, or successful linking.

### REQ-MOLD-002 — Reject other roles and misleading names

1. Assign the canonical mold path to each non-linker role; require rejection.
2. Try `mold-wrapper`, `mold-2`, `not-mold`, `clang`, and `llc` as linker
   basenames; require rejection.
3. Substitute mold for `llc` in the complete manifest; require the exact
   `managed tool projection role/path/digest invalid` error.

### REQ-MOLD-003 — Preserve complete-manifest validation

Starting with the mold linker projection, independently corrupt the linker
digest, omit the `llc` role, duplicate the linker role, and change the format
version. Require, respectively:

| Mutation | Exact expected diagnostic |
|---|---|
| Non-hex digest | `managed tool projection role/path/digest invalid` |
| Missing `llc` role | `managed tool projection incomplete` |
| Duplicate linker | `managed tool role duplicated` |
| Unsupported version | `managed tool projection version invalid` |

## Existing scenarios retained

| Scenario | Production behavior checked |
|---|---|
| Capture-only versus strict activation | Mode alone stays non-strict; either sealed selector activates strict refusal |
| Linux and Windows projections | Eight exact role pins and six environment assignments decode |
| Old, incomplete, duplicate, wrong-tool projections | Invalid projections and duplicate environment entries reject |
| Versioned tool names and role substitution | Existing canonical tool-name rules remain intact |
| Missing and mutated artifact bytes | Descriptor-bound opening and revalidation reject absent or changed files |

The file-admission scenario uses actual temporary files. It remains unrun,
along with the new projection scenarios.

## Qualification boundary

Once a pure-Simple ordinary test CLI is qualified, run this spec with the
existing `test` command and record the executable, source/runtime bindings,
command, and result. No seed fallback is permitted. This patch does not
qualify the r16b test-runner artifact, prove which authority check failed
first in that historical process, or repair the swallowed discovery error.
