# Semantic Markdown source links

Authored companion; runtime/docgen UNRUN. Source: test/03_system/app/doc/feature/semantic_link_lint_spec.spl. REQ-MC-008 B3, using admitted B2 primitive-function snapshots.

1. Prepare a real source and explicit local/GitHub revision bindings. Exercise lint and fix for local fragment/range, colon line and GitHub reference definition. Inspect three warnings and semantic destinations. Reject changed Markdown bytes.
2. Prepare code fences, inline code, a source-looking link label and escaped source text. Exercise critical lint. Inspect zero diagnostics. Reject the negative control by detecting an actual unresolved destination.
3. Prepare one valid and one unknown source destination. Exercise critical lint. Inspect two deny diagnostics. Reject partial fixing when either destination is unresolved.
4. Prepare a configured GitHub blob revision. Exercise a different remote revision and inspect its diagnostic. Reject its fix; then change real source bytes and reject stale local fixing.
5. Prepare actual source and Markdown files. Exercise doc check-links --critical and doc fix-links using explicit authority flags. Inspect nonzero deny result and complete semantic Markdown output. Reject missing required options.

Every scenario uses Prepare the production input / Exercise the production boundary / Inspect the observed result / Reject the negative control. No execution captures or generated-manual quality claim.

6. Construct an externally forged plan replacement after actual-source lint planning. Require apply to reject it against fresh production resolver output. Runtime UNRUN.

7. Prepare an actual parsed function URI in inline and reference destinations. Require configured shared plan and doc CLI check/fix to leave valid Markdown unchanged. Reject malformed/dangling/stale URI and changed source through typed common errors.
8. Prepare a real Markdown file containing a semantic destination. Call the actual process-document checker and require missing explicit source-owner failure. Require fenced/inline code examples to remain protected. This caller deliberately has no positive semantic authority configuration; configured doc CLI supplies the positive counterpart. All execution UNRUN.

## C4 authored counterexamples — UNRUN

The real process generator refuses invalid semantic candidate bytes in both
dry-run and forced publication, preserving exact prior target bytes; ordinary
Markdown remains a positive control. A valid first semantic URI followed by a
bad second URI checks the production batch row and the exact later UTF8
Markdown byte interval. No generic nonzero status or source-text search is an
acceptance oracle.
