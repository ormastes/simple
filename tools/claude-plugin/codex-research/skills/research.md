# Codex Research Skill -- Step 2: Forked Agent Research + Requirement Selection

## Cooperative Phase
**Step 2 of 5** in multi-LLM cooperative pipeline.
- Receives Step 1 output from Claude `/research` (local + domain research)
- Forks parallel Codex research agents to explore alternatives
- Generates requirement draft options with trade-off analysis
- See: `doc/guide/llm_cooperative_dev_phase.md`

**Pipeline:** Step 2 of 5 (research_claude -> **research_codex** -> design_gemini -> design_codex -> design_claude)

## Prerequisites

- OpenAI Codex CLI installed and authenticated (`codex` command available)
- Claude Step 1 research artifacts present in `doc/01_research/`

## Input Artifacts

Read from Claude Step 1:
- `doc/01_research/local/<feature>.md` -- local implementation analysis
- `doc/01_research/domain/<feature>.md` -- domain/external research
- `doc/02_requirements/feature/<feature>_draft.md` -- draft feature requirements (if present)
- `doc/02_requirements/nfr/<feature>_draft.md` -- draft NFR requirements (if present)

## Workflow

### Phase 1: Parse Step 1 Output

1. Read all Step 1 research documents for the target feature
2. Extract key findings: problem statement, proposed solutions, constraints, open questions
3. Identify areas needing deeper exploration or alternative approaches

### Phase 2: Fork Parallel Research Agents

Spawn parallel Codex agents for independent exploration:

- **Agent A (Alternative Approaches):**
  - Explore 2-3 alternative architectures not covered in Step 1
  - Evaluate trade-offs (complexity, performance, maintainability)
  - Use `codex --prompt` with structured research prompt

- **Agent B (Requirement Validation):**
  - Cross-reference draft requirements against codebase constraints
  - Identify missing requirements, conflicts, or over-specifications
  - Use `codex --prompt` with requirement analysis prompt

- **Agent C (Risk & Dependency Analysis):**
  - Analyze implementation risks and dependency chains
  - Check for breaking changes in existing APIs
  - Use `codex --prompt` with risk assessment prompt

### Phase 3: Merge & Generate Options

1. Collect outputs from all parallel agents
2. Deduplicate and reconcile findings
3. Generate 2-3 requirement option sets with trade-off matrix

## Codex CLI Usage

```bash
# Single research query
codex --prompt "Analyze the following research and propose alternative approaches: $(cat doc/01_research/local/<feature>.md)"

# Structured research with system prompt
codex --model codex-mini --prompt "$RESEARCH_PROMPT" --output-format markdown

# Parallel execution (fork agents)
codex --prompt "$AGENT_A_PROMPT" &
codex --prompt "$AGENT_B_PROMPT" &
codex --prompt "$AGENT_C_PROMPT" &
wait
```

## Output Artifacts

Generate to:
- `doc/01_research/codex/<feature>_alternatives.md` -- alternative approach analysis
- `doc/01_research/codex/<feature>_risks.md` -- risk and dependency analysis
- `doc/02_requirements/feature/<feature>_options.md` -- requirement option sets (2-3 variants)
- `doc/02_requirements/nfr/<feature>_options.md` -- NFR option sets

## Output Document Format

```markdown
# <Feature> -- Codex Research (Step 2)
**Date:** YYYY-MM-DD  |  **Status:** Research Phase  |  **Step:** 2/5

## 1. Step 1 Summary (key findings from Claude research)
## 2. Alternative Approaches (2-3 options with trade-offs)
## 3. Requirement Validation (gaps, conflicts, refinements)
## 4. Risk Analysis (breaking changes, dependencies, complexity)
## 5. Requirement Options
### Option A: <name> (conservative)
### Option B: <name> (balanced)
### Option C: <name> (ambitious)
## 6. Recommendation & Trade-off Matrix
```

## Handoff

Pass merged research + requirement options to `/design_gemini` (Step 3) for UI/UX design generation.

## Error Handling

- If Codex CLI is not available, fall back to manual research prompts
- If Step 1 artifacts are missing, prompt user to run `/research` first
- If any parallel agent fails, continue with available results and note gaps
