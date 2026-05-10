# TODO Summary - Visual Overview

**Date:** 2026-01-20
**Total TODOs:** 51 unique items
**Compiler TODOs:** 0 ✅ (100% Complete)

## Priority Distribution

```
P1 (High Priority):     31 items ████████████████████████████████████ 61%
P2 (Medium Priority):    4 items ███ 8%
P3 (Low Priority):      16 items ████████████████ 31%
```

## Category Breakdown

```
┌─────────────────────────────────────────────────────────┐
│ Category Distribution (51 total items)                  │
├─────────────────────────────────────────────────────────┤
│                                                          │
│ 📚 Stdlib Core APIs (12)        ████████████ 24%        │
│ 🔧 Advanced Features (6)        ██████ 12%              │
│ 🐛 DAP Infrastructure (7)       ███████ 14%             │
│ 💡 LSP Features (3)             ███ 6%                  │
│ 🎯 Interpreter (3)              ███ 6%                  │
│ 📝 Linting (2)                  ██ 4%                   │
│ 🌐 Services (4)                 ████ 8%                 │
│ 🔒 Runtime (1)                  █ 2%                    │
│ 🔁 Duplicates/Variations (13)   █████████████ 25%      │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

## Top Blockers (By Impact)

```
┌──────────────────────────────────────────────────────┐
│ Critical Path Items (Unblock Multiple Features)     │
├──────────────────────────────────────────────────────┤
│                                                       │
│ 🔴 #1: File I/O         → Unblocks 15 features      │
│ 🔴 #2: Regex Support    → Unblocks 10 features      │
│ 🔴 #3: CLI Parsing      → Unblocks 10 features      │
│                                                       │
│ Total Impact: 35/51 items blocked (69%)              │
│                                                       │
└──────────────────────────────────────────────────────┘
```

## Implementation Effort

```
Easy (1-2 weeks):       ████████ 8 items
Medium (2-4 weeks):     ████████████████ 16 items
Hard (4-8 weeks):       ███████████████████████████ 27 items
```

## Status by Area

### ✅ Compiler (COMPLETE)
```
[████████████████████████████████████] 100%
2/2 TODOs implemented
```

### 🔴 Stdlib Core APIs (CRITICAL)
```
[░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░] 0%
0/12 implemented - BLOCKING 15+ features
```

### 🟡 Advanced Features (HIGH)
```
[░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░] 0%
0/6 implemented
```

### 🟠 DAP Infrastructure (DEFERRED)
```
[░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░] 0%
0/7 implemented - Needs infrastructure
```

### 🟠 LSP Features (DEFERRED)
```
[░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░] 0%
0/3 implemented - Needs server framework
```

### 🟢 Interpreter (LOW PRIORITY)
```
[░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░] 0%
0/3 implemented
```

## Dependency Tree

```
                    Compiler
                       ✅
                       │
        ┌──────────────┼──────────────┐
        │              │              │
    File I/O       Regex CLI        Other
      🔴            🔴   🔴          APIs
        │              │              │
        └──────────────┼──────────────┘
                       │
              Migration Tools (5)
                   DateTime
                     JSON
                       │
        ┌──────────────┼──────────────┐
        │              │              │
    Context       AST Tools       HashMap
     Pack                          BTreeMap
        │              │              │
        └──────────────┼──────────────┘
                       │
        ┌──────────────┼──────────────┐
        │              │              │
       DAP           LSP          Services
        🟠            🟠              🟢
```

## Priority Actions (Next 30 Days)

```
Week 1-2:  🔴 Implement File I/O
           ├─ File read/write
           ├─ Directory operations
           └─ Path handling

Week 3-4:  🔴 Implement Regex
           ├─ Pattern matching
           ├─ Match groups
           └─ Replace operations

Week 5:    🔴 Implement CLI Parsing
           ├─ Argument parsing
           ├─ Help generation
           └─ Type conversion

Result:    35/51 features unblocked (69%)
```

## Quick Stats

| Metric | Value |
|--------|-------|
| **Total TODOs** | 51 unique |
| **Compiler TODOs** | 0 (✅ Complete) |
| **P1 Critical** | 31 (61%) |
| **Blocked by APIs** | 35 (69%) |
| **Easy to Implement** | 8 (16%) |
| **Hard to Implement** | 27 (53%) |

## Heatmap (Priority × Impact)

```
                  Impact →
                  Low    Med    High
              ┌──────┬──────┬──────┐
         High │  2   │  4   │  25  │ P1: Focus Here! 🔴
Priority   ↓  ├──────┼──────┼──────┤
          Med │  1   │  2   │  1   │ P2
              ├──────┼──────┼──────┤
          Low │  6   │  5   │  5   │ P3
              └──────┴──────┴──────┘
```

**Hotspot:** High Priority × High Impact = 25 items 🔥

## Recommended Focus

### Now (Critical Path)
1. File I/O ⭐⭐⭐
2. Regex ⭐⭐⭐
3. CLI Parsing ⭐⭐⭐

### Soon (Enables Tools)
4. DateTime ⭐⭐
5. JSON ⭐⭐
6. HashMap/BTreeMap ⭐⭐

### Later (Nice to Have)
7. DAP ⭐
8. LSP Enhancement ⭐
9. Services ⭐

## Conclusion

**Compiler:** ✅ Complete (0 TODOs)
**Stdlib:** 🔴 Critical Need (35 blocked features)
**Infrastructure:** 🟠 Deferred (needs frameworks)

**Next Action:** Implement File I/O + Regex + CLI Parsing to unblock 69% of features.

---

For detailed analysis, see: `doc/09_report/todo_categorization_2026-01-20.md`
