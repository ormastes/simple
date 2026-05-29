<!-- codex-research -->
# SPipe Process Harness Domain Research

LLM hook systems vary by provider, but production agent harnesses need the same stable primitives:

- normalized event envelope
- append-only event log
- fast allow/block return code
- durable workflow state
- deployable provider config snippets
- operator HUD with model, VCS, time budget, and goal

Provider hook schemas can change. This implementation keeps provider-specific deploy snippets as generated artifacts under `.spipe/hook-deploy/` and keeps enforcement semantics in common SPipe code.

