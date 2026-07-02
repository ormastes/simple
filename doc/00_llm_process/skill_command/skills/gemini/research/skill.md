<!-- llm-process-gen: managed source=gemini_research_skill source_sha256=0555486f08823e2bb705c62798346c1d5d03ff89b261fd120a08e3188a12955e content_sha256=d57c5b6bfdda2d202e54530c39eafa47713f7a8d876fa0235e753119bff4eff4 -->
# research

Source: `.gemini/commands/research.toml`

Run local + domain research for a feature. Self-sufficient — does not depend on any prior step."

un the research pipeline for the given feature. Self-sufficient — do all steps yourself.

Phase 1: Search src/ and doc/ for related code, types, call chains, prior research, ADRs.
Output: doc/01_research/local/<feature>.md

Phase 2: Web search for external knowledge, papers, prior art.
Output: doc/01_research/domain/<feature>.md

Phase 3: Generate requirement options with pros/cons/effort.
Feature: doc/02_requirements/feature/<feature>_options.md
NFR: doc/02_requirements/nfr/<feature>_options.md

For broad lanes, record lower-model sidecars to use or merge (Codex Spark,
Claude Haiku, Claude Sonnet), or mark N/A. Normal/highest-capability review
must accept broad findings before requirement options, exclusions, or done
marks are trusted.

Phase 4: Ask user to select, then write final requirements.

If another LLM already did research, extend it — never overwrite.
All code in .spl — no Python, no Bash.
"""