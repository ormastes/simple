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

## Coding Standards

| Guide | Description |
|-------|-------------|
| [coding_style.md](coding_style.md) | **Main coding guide** - Domain types, defaults, config patterns, type inference, keyword omission, Lean verification, AOP logging |

**Key rules:** No primitives in public APIs, defaults everywhere, type inference for app code, explicit types for lib code, max 800 lines per file.

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

**Getting Started:**
1. [module_system.md](module_system.md) - Project organization
2. [test.md](test.md) - Writing tests
3. [basic_sample_check.md](basic_sample_check.md) - Verifying your setup

**Building Applications:**
1. [db.md](db.md) - Database integration
2. [web_framework.md](web_framework.md) - Web applications
3. [ui.md](ui.md) - User interfaces

**Advanced Topics:**
1. [vulkan_backend.md](vulkan_backend.md) - GPU programming
2. [context_sharing_usage_guide.md](context_sharing_usage_guide.md) - Advanced module patterns
3. [llm_friendly.md](llm_friendly.md) - LLM integration

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

**Total:** 15 guide documents
