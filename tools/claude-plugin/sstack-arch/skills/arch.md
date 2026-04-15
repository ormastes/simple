# SStack Architecture Skill — Phase 3: Architect

**Trigger:** `/sstack-arch` or when a feature with `Phase: research-done` needs system design.

## What This Skill Does

Designs system architecture and module plan based on research findings. Produces a module plan, dependency map, architecture decisions, and public API surface. Appends architecture doc to the state file.

## When to Use

- After Phase 2 (research) completes with `Phase: research-done`
- When you need to decide module structure, file locations, and dependencies
- When architecture decisions need explicit rationale (ADR-style)

## Workflow

1. Read `.sstack/<feature>/state.md` — extract requirements and research summary
2. Design the module structure: which files, where they live, what each does
3. Define the dependency map between modules (no circular deps allowed)
4. Make explicit architecture decisions (ADR-style: context, decision, consequences)
5. Specify file paths for every new or modified file
6. Append architecture to the state file (do not modify earlier sections)

## Boundaries (Boil a Small Lake)

- ONLY architecture decisions
- Do NOT write implementation code (signatures and type names only)
- Do NOT write test files
- Do NOT redo research — that phase is done
- Context budget: sub-40%

## Entry Criteria

- `.sstack/<feature>/state.md` exists with `Phase: research-done`
- Research summary and requirements are present

## Exit Criteria

- State file contains `## Architecture` with:
  - Module list with file paths (new and modified)
  - Dependency map (A depends on B, no cycles)
  - Architecture decisions with rationale
  - Public API surface (function signatures, type names)
- No circular dependencies in the module graph
- Every REQ-N is covered by at least one module
- `## Phase` updated to `arch-done`

## State File Additions

```markdown
## Architecture

### Module Plan
| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| <name> | `src/path/file.spl` | <purpose> | New |
| ...    | ...  | ...  | Modified |

### Dependency Map
- `module_a` -> `module_b` (uses X)
- `module_b` -> `std.text` (string ops)
- No circular dependencies: verified

### Decisions
- **D-1:** <decision> — because <rationale>
- **D-2:** <decision> — because <rationale>

### Public API
- `fn name(args) -> ReturnType` — <purpose>
- `class TypeName` — <purpose>
- ...

### Requirement Coverage
- REQ-1 -> module_a
- REQ-2 -> module_b
- ...

## Phase
arch-done

## Log
- intake: Created state file with N acceptance criteria
- research: Found N reusable modules, N existing files, N requirements drafted
- arch: Designed N modules, N decisions, no circular deps
```

## Next Phase

Hand off to **sstack-spec** (Phase 4: QA Lead) once `Phase: arch-done` is set.
