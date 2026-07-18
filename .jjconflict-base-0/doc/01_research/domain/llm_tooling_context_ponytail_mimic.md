# Domain Research: LLM Context and Minimalism Tooling

Date: 2026-06-25

## Context Tools

Useful LLM context tools share a few stable behaviors:

- gather local evidence without pasting full raw output into the conversation
- index or summarize large content before returning it
- support query-focused retrieval
- preserve provenance labels so later reviews can trace evidence
- prefer deterministic local artifacts over ephemeral chat-only summaries

The installed context-mode connector demonstrates this shape through
`ctx_batch_execute`, `ctx_fetch_and_index`, and `ctx_insight`.

## Minimalism / Ponytail Tools

Minimalism assistants are useful when they are policy checks over concrete
artifacts:

- identify duplicated or speculative code
- prefer existing helpers over new abstractions
- ask whether a feature needs to exist before building it
- keep recommendations one finding per actionable cut

They are less useful as a large framework. The repo-native replacement should be
an evidence/report surface that can be run by SPipe and reviewed by a normal
LLM, not a second agent runtime.

## Design Implication

Split the goal:

1. **Context pack generation**: deterministic file-to-pack function and CLI.
2. **Context index/search**: later, append/index stored packs with query lookup.
3. **Ponytail review**: later, report simplification candidates over a diff or
   pack, reusing context-pack content.
4. **Dashboard visibility**: later, expose pack/review summaries in the LLM
   dashboard diagnostics/task panels.

This avoids building a daemon before the local packer works.

