# Simple Language Guides

**Purpose:** Operational guides and practical tutorials for using Simple language features and tools.

**Last Updated:** 2025-12-28

---

## Overview

This directory contains practical guides for:
- Using language features effectively
- Working with the test framework
- Integrating with databases and web frameworks
- Building UI applications
- Contributing to Simple development

**Difference from other docs:**
- **[doc/spec/](../spec/)** - Language specifications (what the language supports)
- **[doc/research/](../research/)** - Technical research (why/how decisions were made)
- **[doc/guides/](.)** - Practical how-to guides (how to use features)

---

## Production-Ready Features ✅

**NEW! These features are FULLY FUNCTIONAL and tested!**

| Guide | Status | Tests | Description |
|-------|--------|-------|-------------|
| [async_guide.md](async_guide.md) | ✅ READY | 9/9 PASS | **Async/await programming** - Lambdas, futures, generators, actor model (all <10ms) |
| [lsp_integration.md](lsp_integration.md) | ✅ READY | 8/8 PASS | **Language Server Protocol** - VS Code, Neovim, Emacs setup; go-to-def, hover, completion |
| [backend_capabilities.md](backend_capabilities.md) | ✅ READY | 9/9 PASS | **Compiler backends** - Cranelift, LLVM, Native selection; capability detection |

**See also:** [FEATURES_THAT_WORK.md](../FEATURES_THAT_WORK.md) for complete list of working features.

---

## Language Reference

| Guide | Description |
|-------|-------------|
| [syntax_quick_reference.md](syntax_quick_reference.md) | **Syntax cheatsheet** - Slicing `[1:5]`, comprehensions, `?.`, `??`, destructuring, ranges, all implemented syntax |
| [fn_lambda_syntax.md](fn_lambda_syntax.md) | Function and lambda syntax details |

---

## Coding Standards

| Guide | Description |
|-------|-------------|
| [coding_style.md](coding_style.md) | **Main coding guide** - Domain types, defaults, config patterns, type inference, keyword omission, Lean verification, AOP logging, doctest examples |
| [sspec_writing.md](sspec_writing.md) | **SSpec test guide** - BDD tests, document format, doctest integration, matchers, fixtures |
| [architecture_writing.md](architecture_writing.md) | **Architecture guide** - Skeleton-first design, Lean verification workflow, diagram generation from tests |
| [design_writing.md](design_writing.md) | **Design guide** - Draft diagrams replaced by test-generated class/sequence diagrams |
| [application_writing.md](application_writing.md) | **Application guide** - Building apps with links to spec/generated manuals, GUI/TUI/Web/CLI patterns |

**Key rules:** No primitives in public APIs, defaults everywhere, type inference for app code, explicit types for lib code, doctest for all public APIs, max 800 lines per file.

**Architecture workflow:** Skeleton → Verify → Test → Diagram

**Design workflow:** Draft → Test → Generate → Replace

---

## Testing & Quality

### Test Framework

| Guide | Purpose | Topics Covered |
|-------|---------|----------------|
| [test.md](test.md) | **Main test policy** | BDD framework, mock control, coverage tracking, test levels (unit/integration/system) |
| [test_guides.md](test_guides.md) | **Architecture testing** | Test pyramid, layer dependencies, interface contracts, architecture validation (features #936-945) |
| [system_test.md](system_test.md) | **System test framework** | E2E testing, CLI testing, out-of-process tests |
| [basic_sample_check.md](basic_sample_check.md) | **Sample verification** | Verifying test setup works correctly |

**Quick Start:** Read [test.md](test.md) for the main test policy. For architecture testing, see [test_guides.md](test_guides.md).

### Dependency Tracking

| Guide | Description |
|-------|-------------|
| [depedency_tracking.md](depedency_tracking.md) | Module dependency analysis (note: typo in filename) |
| [context_sharing_usage_guide.md](context_sharing_usage_guide.md) | Sharing context across modules |

---

## Frameworks & Libraries

### Database Integration

| Guide | Description | Status |
|-------|-------------|--------|
| [db.md](db.md) | Database integration overview | Active |
| [db_part1.md](db_part1.md) | Database design (part 1) | Note: Consider merging |
| [db_part2.md](db_part2.md) | Database implementation (part 2) | Note: Consider merging |
| [sqp.md](sqp.md) | SQL-like query language (SQP) | Design |

**Note:** db_part1.md and db_part2.md should be merged into a single comprehensive guide.

### Web Framework

| Guide | Description |
|-------|-------------|
| [web_framework.md](web_framework.md) | Web framework architecture and usage |

### UI Development

| Guide | Description |
|-------|-------------|
| [ui.md](ui.md) | UI framework overview (TUI, GUI) |
| [vulkan_backend.md](vulkan_backend.md) | Vulkan GPU backend for graphics |

---

## Module System

| Guide | Description |
|-------|-------------|
| [module_system.md](module_system.md) | Import/export, __init__.spl, package organization |

**See also:** [doc/spec/modules.md](../spec/modules.md) for module system specification.

---

## LLM-Friendly Development

| Guide | Description |
|-------|-------------|
| [llm_friendly.md](llm_friendly.md) | Guidelines for making code LLM-friendly |

Covers:
- IR export for AI code review
- Context packs for LLM consumption
- Lint framework for code quality
- Best practices for AI-assisted development

---

## Guide Organization

### By Purpose

**NEW! Production-Ready Features:**
1. [async_guide.md](async_guide.md) - ✅ **Async/await guide** (9 tests passing)
2. [lsp_integration.md](lsp_integration.md) - ✅ **LSP editor setup** (8 tests passing)
3. [backend_capabilities.md](backend_capabilities.md) - ✅ **Compiler backends** (9 tests passing)

**Getting Started:**
1. [syntax_quick_reference.md](syntax_quick_reference.md) - **Language syntax cheatsheet** (slicing, comprehensions, `?.`, `??`, etc.)
2. [coding_style.md](coding_style.md) - Coding conventions
3. [sspec_writing.md](sspec_writing.md) - Writing tests with SSpec
4. [module_system.md](module_system.md) - Project organization
5. [basic_sample_check.md](basic_sample_check.md) - Verifying your setup

**Building Applications:**
1. [application_writing.md](application_writing.md) - Application patterns with spec links
2. [db.md](db.md) - Database integration
3. [web_framework.md](web_framework.md) - Web applications
4. [ui.md](ui.md) - User interfaces

**Advanced Topics:**
1. [architecture_writing.md](architecture_writing.md) - Skeleton-first architecture
2. [design_writing.md](design_writing.md) - Draft-to-generated diagrams
3. [vulkan_backend.md](vulkan_backend.md) - GPU programming
4. [context_sharing_usage_guide.md](context_sharing_usage_guide.md) - Advanced module patterns
5. [llm_friendly.md](llm_friendly.md) - LLM integration

---

## Related Documentation

- **[doc/spec/](../spec/)** - Language specifications
- **[doc/status/](../status/)** - Implementation status
- **[doc/research/](../research/)** - Technical research
- **[doc/plans/](../plans/)** - Roadmap and plans

---

## Contributing Guides

When adding new guides:
1. Use descriptive names (topic + "guide" or just topic)
2. Focus on practical usage, not specification
3. Include code examples and common patterns
4. Add troubleshooting section if applicable
5. Update this README in appropriate category

**Guidelines:**
- Guides are HOW-TO documents
- Specifications (doc/spec/) are WHAT-IS documents
- Research (doc/research/) are WHY documents
- Keep guides practical and example-driven

---

## Known Issues

**File naming:**
- `depedency_tracking.md` - Typo in filename (should be "dependency")

**Split files:**
- `db_part1.md` and `db_part2.md` - Should be merged into single comprehensive guide

---

## Recent Updates (2026-02-14)

**Major Documentation Update:**

Added 3 comprehensive guides for production-ready features (1700+ lines total):
- ✅ `async_guide.md` - Complete async/await programming guide
- ✅ `lsp_integration.md` - LSP setup for all major editors
- ✅ `backend_capabilities.md` - Compiler backend selection guide

**Test Audit Results:**
- 30+ tests previously marked @skip/@pending actually PASS!
- Async/await: 9/9 tests passing
- LSP infrastructure: 8/8 tests passing
- Compiler backends: 9/9 tests passing

**See:** [FEATURES_THAT_WORK.md](../FEATURES_THAT_WORK.md) for details.

---

**Total:** 23 guide documents (+3 new)
