# Exact provider CLI version research

**LOCAL_READONLY_RESEARCH / SOURCE_INSPECTED / NOT_NATIVE_QUALIFICATION**.
Only --version, --help and read-only subcommand help were executed. No task,
login, auth-status operation, session mutation or billing action was executed.
Raw outputs remain in `/tmp/caret-provider-cli-probes-20261115-sol`.

| Provider | Observed stdout |
|---|---|
| Codex | `codex-cli 0.169.0` |
| Claude Code | `2.1.325 (Claude Code)` |
| Gemini CLI | `0.68.0` |
| Kimi | `2.5.3` |

Help and official primary documentation establish the adapter's selected argv
forms; later container-installed versions must be observed independently by
their actual admitted common owner. Local research subprocesses do not provide
that capability and do not bind a future mutable path or container image.

## Gemini 0.68.0 exact stable session IDs

Installed package metadata says `@google/gemini-cli` version `0.68.0`; its file
SHA256 is `3251e00608874812d7327f41cddb09a6f8e13613124c36d21fbf537e2510bbaa`.
The launcher `bundle/gemini.js` SHA256 is
`fcc38edd4f864c2f5fa582d7d133c19b1a04c697ad3143ab8045f92b77644c68`.
It dynamically imports `gemini-Q2FNZWQG.js` (SHA256
`686cac58494e29c2c5ab33568daa90be4fd37fbc03a0a702c8b46b6296fe7525`),
whose active SessionSelector import comes from `chunk-VFM6AETN.js` (SHA256
`a2f67a42ee46a7d34bcb0f21fd779396a03d3d8f62a1908f297047ccae7a57d5`).

The active CLI calls `sessionSelector.resolveSession(resumeArg)` at line 18719.
The active selector's `findSession` compares `session.id === trimmedIdentifier`
at lines 31605–31609 before considering numeric indexes. Its normal resume path
does not perform a prefix match. The package's bundled source attribution names
`packages/cli/src/utils/sessionUtils.ts`.

Independently fetched official pinned source at
[Gemini CLI v0.68.0 sessionUtils.ts](https://github.com/google-gemini/gemini-cli/blob/v0.68.0/packages/cli/src/utils/sessionUtils.ts)
has Git blob SHA `0bcd8768d10e8cfd355230db677b361a140bb4b1` and the same
full-ID comparison. Therefore this adapter accepts full UUIDs only and rejects
names, prefixes, latest and numeric indexes. A syntactically valid UUID is still
DATA; it proves neither that a session exists nor that its scope is authorized.

## Kimi 2.5.3 mode precision

The installed help calls `--yolo` Ask When Needed and `--auto` Never Ask; those
flags must not be conflated. The current official command reference documents
headless automatic defaults, but the adapter need not claim an internal
permission mode as proof: every task already requires genuine containment.

Official pinned repository is **MoonshotAI/kimi-code**, tag
`@moonshot-ai/kimi-code@2.5.3` (the older kimi-cli repository has no matching
v2.5.3 tag). Pinned `apps/kimi-code/package.json` is version 2.5.3, Git blob
`cea660f2dfe678c4c7d1702113bf1964dec68e59`.
[Pinned options.ts](https://github.com/MoonshotAI/kimi-code/blob/%40moonshot-ai%2Fkimi-code%402.5.3/apps/kimi-code/src/cli/options.ts),
blob `eea67caf716da92d462648beced14c31180d10c8`, explicitly rejects prompt mode
combined with yolo, auto or plan flags. The planner adds none of them and
preserves the existing headless default instead of inventing an equivalent
approval policy. This source evidence does not qualify native container
execution, authentication state or task settlement.
