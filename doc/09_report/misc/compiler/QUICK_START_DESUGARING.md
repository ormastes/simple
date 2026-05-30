# Quick Start: Making Full Simple Compilable by Core

**Goal:** Enable Core Simple (seed-compilable) to build Full Simple (compiler)

---

## TL;DR

Full Simple uses features (generics, impl blocks, closures) that Core can't compile.
Solution: **Desugar** Full → Core by mechanical transformations.

**Status:** ✅ Research done | 🚀 Prototype started | 📋 Plan ready

---

## Key Files

| File | Purpose | Size |
|------|---------|------|
| [IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md) | **START HERE** - Current status | 9.4 KB |
| [CORE_FULL_COMPILATION_PLAN.md](CORE_FULL_COMPILATION_PLAN.md) | Quick reference guide | 9.3 KB |
| [DESUGARING_PLAN.md](DESUGARING_PLAN.md) | Complete strategy | 13.5 KB |
| [LEXER_DESUGARING_EXAMPLE.md](LEXER_DESUGARING_EXAMPLE.md) | Detailed examples | 11.5 KB |

---

## What's Been Done

### ✅ Documents Created (4 files, ~43 KB)
- Complete analysis of Core vs Full Simple
- 6 transformation types documented with examples
- 5-week implementation roadmap
- Success criteria and verification strategy

### ✅ Prototype Started
- **src/compiler_core_legacy/lexer_desugared.spl** - 150 lines of Core-compatible code
- Demonstrates all major transformations:
  - `impl` blocks → module functions
  - `Option<T>` → tagged fields
  - Pattern matching → if-else chains
  - Method calls → function calls

---

## The Problem

```
┌─────────────────────────────────────────┐
│  SEED (C++ Runtime)                     │
│  Can only compile → Core Simple         │
└──────────────┬──────────────────────────┘
               ↓
┌─────────────────────────────────────────┐
│  CORE SIMPLE (Restricted)               │
│  ❌ No: impl, generics, closures        │
│  ✅ Only: functions, concrete types     │
└──────────────┬──────────────────────────┘
               ↓ ⚠️ PROBLEM: Can't compile Full!
┌─────────────────────────────────────────┐
│  FULL SIMPLE (Complete Language)        │
│  ✅ Has: impl, generics, closures       │
│  ✅ This is the compiler implementation │
└─────────────────────────────────────────┘
```

---

## The Solution

**Desugar** Full Simple → Core Simple:

```
Full Simple (impl, generics, closures)
  ↓ [Desugarer Tool]
Core Simple (functions, concrete types)
  ↓ [Seed Compiler]
C++ Code
  ↓ [g++]
Binary
```

---

## Example Transformation

### Before (Full Simple)
```simple
impl Lexer:
    me next() -> Token:
        if self.pending_token.?:
            return self.pending_token.unwrap()
        # ...
```

### After (Core Simple)
```simple
fn lexer_next(self: Lexer) -> Token:
    if self.has_pending_token:
        return self.pending_token_value
    # ...
```

---

## Next Steps

### Immediate (Today)
```bash
# View the prototype
cat src/compiler_core_legacy/lexer_desugared.spl

# Read the status
cat IMPLEMENTATION_STATUS.md
```

### This Week
1. Complete manual lexer.spl conversion (1,430 lines)
2. Test with seed compiler
3. Document learnings

### Next 2-3 Weeks
4. Build automated desugarer tool
5. Apply to 5-10 more files
6. Test compilation

### Month 1
7. Desugar all 52K lines
8. Full test suite
9. Bootstrap verification

---

## Effort Estimate

- **Manual prototype:** 8 hours (20% done)
- **Automated tool:** 2-3 weeks
- **Full coverage:** 1 week
- **Testing:** 3-5 days
- **TOTAL:** 3-4 person-weeks

---

## Directory Structure

```
simple/
├── QUICK_START_DESUGARING.md          ← You are here
├── IMPLEMENTATION_STATUS.md            ← Current status
├── CORE_FULL_COMPILATION_PLAN.md      ← Quick reference
├── DESUGARING_PLAN.md                  ← Complete plan
├── LEXER_DESUGARING_EXAMPLE.md        ← Detailed examples
│
├── src/
│   ├── compiler/                       ← Full Simple (52K lines)
│   ├── compiler_core_legacy/                  ← Desugared output ✨ NEW
│   │   └── lexer_desugared.spl         ← Prototype (150 lines)
│   ├── core/                            ← Core Simple (8.8K lines)
│   └── tools/                           ← Desugarer tool ✨ NEW
│       └── DESUGARER_README.md
│
└── bootstrap/
    └── seed.cpp                         ← C++ runtime (143K lines)
```

---

## Read Next

1. **[IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md)** - Detailed progress report
2. **[CORE_FULL_COMPILATION_PLAN.md](CORE_FULL_COMPILATION_PLAN.md)** - Quick reference
3. **[src/compiler_core_legacy/lexer_desugared.spl](src/compiler_core_legacy/lexer_desugared.spl)** - Prototype code

---

**Questions?** See planning documents above or check the prototype code!
