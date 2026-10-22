# Revision-bound ast-link commands

Authored companion; runtime/docgen UNRUN. Source: test/03_system/app/ast_link/feature/semantic_from_line_spec.spl. REQ-MC-008 B2 partial primitive-function producer.

1. Prepare a real two-function file and its SHA256 revision. Exercise from-line at the second function header and body. Inspect identical short URIs naming that function. Reject a range spanning both functions.
2. Prepare a one-function file. Exercise from-line command then resolve command with explicit package/module/file/revision authority. Inspect the actual file:1:1 result. Reject line zero.
3. Prepare a parsed snapshot. Exercise a past-EOF range and inspect InvalidSpan. Change source bytes and reject the old snapshot with RevisionChanged.
4. Prepare a real parsed declaration. Duplicate its public interval as a corrupt snapshot negative control. Require actual-source reauthentication to discard both caller-owned intervals and select the genuine declaration.
5. Prepare one real parsed function URI. Exercise an ordered two-item batch and inspect matching stable identities. Reject a batch containing a stale fingerprint without publishing partial output.

Each scenario uses Prepare the production input / Exercise the production boundary / Inspect the observed result / Reject the negative control steps. No captured execution evidence or generated-manual quality claim.

6. Forge an invented declaration/index using a real file and matching SHA256. Require real URI resolution to restore the actual ID/span, invented URI refusal, and from-line selection to ignore the forged interval. Runtime UNRUN.
