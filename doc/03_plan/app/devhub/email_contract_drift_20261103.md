# DevHub email contract drift: bounded repair

Canonical record: `devhub_email_contract_drift_2026_10_19` (P2, open).
Base: release commit `d591d1df36f4bad9692c8eeab65c1a3a7ba69e6e`.
Status: source repair / AUTHORED_UNRUN; no bug closure or runtime PASS.

The checked configuration owner is `src/app/devhub/email_support.spl`.
Legacy mail-cli JSON uses provider `outlook` for IMAP unless `protocol` is
`graph`; its importer in `tools/mail-cli/lib/config.bash` explicitly normalizes
that spelling. Shared SDN retains `outlook` for Graph and `outlook_imap` for
IMAP. The facade previously mapped both formats' Outlook spelling to Graph.
The repair uses the explicit `.json` selection already employed by the loader;
explicit Graph and shared SDN behavior remain intact.

The JSON checked loader previously validated only root/accounts containers,
then silently dropped nonobject accounts or converted malformed routing and
credential fields to empty text. The repair rejects malformed account entries,
default-account types and account-field types before mapping. Numeric port
fields remain accepted for legacy compatibility. This is structural validation,
not a new credential policy or complete port/protocol semantic validator.

Spec-first commit `4454567736c` contains ten local fixture scenarios under
`test/01_unit/app/devhub/email_contract_drift_spec.spl`. They call production
parsing/loading owners and never execute mail, password commands, Graph or
network requests. Exact provider and error-code assertions cover both new
rejections and valid compatibility controls. The malformed fixtures contain no
real secrets. Existing broad email routing specs remain unchanged.

Other report facets were inspected without speculative edits: unknown action
and existing usage paths already return 1; missing mail binary on inbox returns
1 as its current spec expects; `tools/mail-cli/lib/inbox.shs` exists and loads
the Bash implementation. These source observations do not qualify runtime
behavior or establish that every historical exit/path symptom is resolved.

Validation: no admitted self-hosted runtime is available in this lane and no
bootstrap/seed fallback is authorized. Thus the tests have not demonstrated RED
or GREEN, and spipe-docgen/manual generation has not run. The authored companion
is labeled accordingly. Source whitespace, environment-runtime guards and
executable-spec layout checks are the limited static checks. No requirement
options or provider APIs were added. Two source-repair cycles maximum per cause.

Ownership: this isolated branch owns only its new spec/plan/manual and the
email_support changes. Prior crypto/reference docs are separate commits. Astra
reviews the exact candidate; root/land_source_repairs owns integration/landing.
