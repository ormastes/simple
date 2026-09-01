# Unified lifecycle acceptance evidence

**Scope:** agent-owned observe-only base, 2026-08-25.  A diagnostic PASS below
does not satisfy the production gate while `bin/simple` is the Rust seed.

| Criterion | Base status | Evidence or remaining condition |
|---|---|---|
| AC-1 | Implemented in source; diagnostic codec PASS | Typed codecs cover every named entity, traverse digest-bound envelopes, and reject schema/digest/missing/duplicate/unknown-field input. Final authoritative run is pending. |
| AC-2 | Implemented; diagnostic PASS | `identity.spl`; rewrite and alias-validation examples. |
| AC-3 | Implemented; diagnostic PASS | `review.spl`; exact-revision approval/gate examples. |
| AC-4 | Implemented; diagnostic PASS | `.spipe/policy/vcs.sdn`, `src/app/sj/lifecycle_policy.spl`; fail-closed policy examples. |
| AC-5 | Implemented, observe-only | `src/app/sj/operation.spl`; legacy push maps to a typed dry-run operation. No protected writer was enabled. |
| AC-6 | Implemented; diagnostic PASS | `integrate_plan.spl` and `gate_manifest.spl`; pinned revision, CAS, manifest and refusal examples. |
| AC-7 | Implemented base | Stored local inspection, integrity rejection, escaped versioned output, capability-explicit provider traits, idempotency identity, and observe-only dry-run refusal are present. |
| AC-8 | Implemented; diagnostic PASS | `sync.spl`; durable conflict and replay-safe outbox examples. |
| AC-9 | Implemented; diagnostic PASS | `release/version.sdn`, `version_manifest.spl`; malformed prerelease and projection checks. Rendering is plan-only. |
| AC-10 | Implemented; diagnostic PASS | `release.spl` and release records; invalid transition/immutability examples. Live publication is excluded from the base. |
| AC-11 | Implemented; diagnostic PASS | `work.spl`, feature manifest and separation examples. |
| AC-12 | Implemented in source | The executable trace inventory requires all 18 rows, existing evidence paths, and matching `# @ac:` tags for every unblocked criterion. Authoritative execution awaits an admitted pure-Simple CLI. |
| AC-13 | Blocked | Manual mirrors the five frozen steps and has zero known stubs; `sspec-maintain` cannot execute on the deployed seed. Independent review remains open. |
| AC-14 | Partially evidenced | Zero lint errors, no new raw runtime/env/process calls, files remain below 800 lines. Coverage and duplicate-check await the admitted CLI. |
| AC-15 | Implemented in source | One pure-Simple code path exposes typed lifecycle/review/task/knowledge/release provider traits; no OS fork or new runtime boundary was added. |
| AC-16 | Implemented for base | Research, requirements, architecture, design, plans, guide, expert docs, feature manifest, state and known blocker record are linked. |
| AC-17 | Source-complete | State records every unaffected command/skill surface and why; independent source review found the operator manual adequate. Authoritative generated-manual dimensions remain under AC-13. |
| AC-18 | Blocked | Diagnostic focused tests/lint are green. Production verification, duplicate scan, coverage, affected full checks, and working-tree guards require the admitted CLI and unrelated lane cleanup. |

## Promotion decision

The base is suitable for continued shadow-mode development only. It does not
authorize protected-ref mutation, provider publication, release tagging, or
SCV content authority. Promotion requires AC-13, AC-14, AC-17, and AC-18 to
close with authoritative evidence and the later migration-stage exit gates.
