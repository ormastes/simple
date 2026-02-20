# Plan Documentation

Project plans defining why, scope, milestones, and risks.

Plan answers: **What and when?**

Plans are living documents — update as work progresses, delete when 100% complete (git history preserves past plans).

---

## Plan Document Template

```markdown
# Project Plan – [Feature Name]

## 1. Objective
Deliver [capability] for [milestone].

## 2. Scope
IN:
- Capability A
- Capability B

OUT:
- Deferred item X
- Future enhancement Y

## 3. Milestones
- Week 1: Requirements finalized
- Week 2: Design complete
- Week 3–4: Implementation
- Week 5: Testing and hardening

## 4. Risks
- Risk A: mitigation
- Risk B: mitigation

## 5. Success Metrics
- Metric 1: target value
- Metric 2: target value

## Cross-References
- **Requirements:** [doc/requirement/xxx.md](../requirement/xxx.md)
- **Design:** [doc/design/xxx.md](../design/xxx.md)
- **Research:** [doc/research/xxx.md](../research/xxx.md)
```

---

## Active Plans

**Status:** Active Planning Phase
**Created:** 2026-02-13

---

## Overview

Two major cleanup initiatives:

1. **Stdlib Refactoring** - Split 114 large utils files into focused modules
2. **TODO Implementation** - Fix 806 TODO items across codebase

---

## Active Plans

### 1. REFACTOR_PHASES.md
**Goal:** Refactor stdlib utils files into modular subdirectories

- **Scope:** 114 files (~103k lines)
- **Duration:** 20 weeks (Feb 13 - Jul 2, 2026)
- **Status:** Phase 1 - Critical Size (4 files)
- **Progress:** 8/114 files complete (7%)

**Quick Start:**
```bash
cd src/lib
# Work on current phase
cat ../../doc/plan/REFACTOR_PHASES.md
```

---

### 2. TODO_PHASES.md
**Goal:** Implement and remove all TODO items

- **Scope:** 806 TODOs in source code
- **Duration:** 8 months (Feb 13 - Sep 30, 2026)
- **Status:** Planning Phase
- **Progress:** Not started

**Quick Start:**
```bash
# View TODOs
bin/simple todo-scan
cat doc/TODO.md

# Work on current phase
cat doc/plan/TODO_PHASES.md
```

---

## Completion Process

### After Each Phase Completes

**For Refactoring:**
1. All module tests pass
2. Original `*_utils.spl` deleted
3. Phase marked complete with ✅
4. Commit: `jj describe -m "refactor: Phase N complete"`

**For TODOs:**
1. Feature implemented
2. TODO comment removed
3. Tests pass
4. Phase marked complete with ✅
5. Commit: `jj describe -m "fix: Implement <feature>"`

### When ALL Plans Complete

**Delete this entire directory:**
```bash
rm -rf doc/plan/
jj describe -m "chore: Remove completed planning docs"
```

---

## Why Delete After Completion?

- **No dead documentation** - Plans are temporary
- **Git history preserves** - Can always view past plans
- **Clean repository** - Only active docs remain
- **Clear signal** - Empty `doc/plan/` means work is done

---

## Current Focus

**Week of 2026-02-13:**
- Verify Phase 0 refactoring (8 modules)
- Complete json/ module split
- Start numerical_methods/ split
- Categorize all TODOs

**Next milestone:** Phase 1 refactoring complete (4 files)

---

## Notes

- Plans are living documents - update as work progresses
- Mark items complete with ✅ emoji
- Commit frequently for easy rollback
- Delete plans only when 100% complete

**Last Updated:** 2026-02-13
