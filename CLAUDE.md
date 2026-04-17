# Simple Language Compiler

**Self-hosted compiler written in Simple.** Bootstrap: Rust seed → Simple compiler → self-hosted binary.
Impl in Simple unless it has big performance differences.

## Essential Commands
```bash
bin/simple build                  # Debug build (lint/fmt/check/bootstrap subcommands also available)
bin/simple test                   # Run all tests (or: test path/to/spec.spl)
scripts/bootstrap/bootstrap-from-scratch.sh --deploy  # Full bootstrap
```

## Critical Rules
- **jj** for VCS — `jj commit -m "msg"` / push: `jj bookmark set main -r @- && jj git push --bookmark main`
- **NEVER create branches** — work directly on `main`
- **ALL code in `.spl`/`.shs`** — no Python/Bash (except 3 bootstrap scripts)
- **NO inheritance** — use composition, traits, mixins. **Generics:** `<>` not `[]`
- **NEVER skip** failing tests without approval. **NEVER convert TODO to NOTE** — implement or delete
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- **NEVER over-engineer.** **DO NOT ADD REPORT TO GIT** unless requested
- **MDSOC+ by default** — use MDSOC outer + ECS business layer for userland services/apps; kernel/drivers stay MDSOC-only. See `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+ section)

## Detailed Rules & Reference
- **Rules:** `.claude/rules/` — `language.md`, `testing.md`, `bootstrap.md`, `commands.md`, `structure.md`, `code-style.md`, `vcs.md`
- **Skills:** `.claude/skills/` — invoke `/skill-name` (`/sstack`, `/dev`, `/coding`, `/test`, `/debug`, etc.)
- **Agents:** `.claude/agents/` — `code`, `test`, `debug`, `explore`, `docs`, `vcs`, `infra`, `build`, `ml`
- **Memory refs:** `.claude/memory/ref_*.md` — architecture, coding, SFFI, stdlib, CUDA, etc.
- **Syntax:** `doc/07_guide/quick_reference/syntax_quick_reference.md`
