# feature.md Updates Required

**Date:** 2025-12-23
**Purpose:** Mark 40 verified AOP features as complete in feature.md
**Current Status:** 40/49 features verified complete (82%)

## Features to Mark as ✅ Complete

### Phase 1: Predicate Grammar (#1000-1005) - 6 features

```markdown
| #1000 | `pc{...}` syntactic island (lexer mode) | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate_parser.rs` |
| #1001 | Predicate operators (!, &, \|, grouping) | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate_parser.rs` |
| #1002 | Pattern wildcards (*, **, prefix*, *suffix) | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1003 | Signature pattern `ret_pat qname_pat(arg_pats)` | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1004 | `..` argument wildcard | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1005 | Allowed introducer validation | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
```

### Phase 2: Context Validation (#1006-1008) - 3 features

```markdown
| #1006 | Weaving selector set validation | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1007 | DI/Mock selector set validation | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1008 | Illegal selector in context diagnostic | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
```

### Phase 3: Hybrid DI (#1009-1015) - 7 features
(Already marked #1009 and #1013 as complete in previous session)

```markdown
| #1010 | SDN `di:` section with profiles | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/di.rs` |
| #1011 | `bind on pc{...} -> Impl scope priority` syntax | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/di.rs` |
| #1012 | `@sys.inject` constructor injection | 3 | ✅ | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/di/` | `src/compiler/tests/di_injection_test.rs` |
| #1014 | Priority/specificity/stable-order resolution | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/di.rs` |
| #1015 | Ambiguous binding diagnostic | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/di.rs` |
```

### Phase 5: AOP Mocking (#1020-1025) - 6 features

```markdown
| #1020 | `mock Name implements Trait:` syntax | 3 | ✅ | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/compiler/src/mock.rs` |
| #1021 | `expect method() -> Type:` syntax | 2 | ✅ | S+R | [aop.md](../research/aop.md) | `std_lib/test/system/mock/` | `src/compiler/src/mock.rs` |
| #1022 | `@sys.test_only` decorator enforcement | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/mock.rs` |
| #1023 | Mock binding via DI predicates (test profile) | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/mock.rs` |
| #1024 | Illegal mock in non-test diagnostic | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/mock.rs` |
| #1025 | Illegal Mock* binding outside test profile | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/mock.rs` |
```

### Phase 6: Architecture Rules (#1026-1033) - 8 features

```markdown
| #1026 | `arch_rules:` block syntax | 2 | ✅ | S+R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1027 | `forbid pc{...}` rule | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1028 | `allow pc{...}` rule | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1029 | `import(from_pattern, to_pattern)` selector | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1030 | `depend(from_pattern, to_pattern)` selector | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1031 | `use(pattern)` selector | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1032 | `export(pattern)` selector | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
| #1033 | `config(STRING)` selector | 2 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/arch_rules.rs` |
```

### Phase 7: Compile-Time Weaving (#1036-1046) - 11 features

```markdown
| #1036 | `execution(signature)` join point | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1037 | `within(pattern)` join point | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1038 | `attr(IDENT)` join point | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1039 | `effect(effect_set)` join point | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1040 | `test(IDENT)` join point | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1041 | `decision()`/`condition()` join points (coverage) | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1042 | Zero-overhead when aspects.enabled = [] | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1043 | `before` advice | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1044 | `after_success` advice | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1045 | `after_error` advice | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
| #1046 | Advice priority ordering | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/weaving.rs` |
```

### Phase 8: Link-Time & Runtime (#1047-1048) - 2 features

```markdown
| #1047 | `call(signature)` link-time selector | 4 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
| #1048 | `init()` selector (runtime) | 3 | ✅ | R | [aop.md](../research/aop.md) | - | `src/compiler/src/predicate.rs` |
```

Note: #1048 not in current feature.md, only #1047 exists

## Summary Statistics Update

Update the summary line in feature.md:

**Current:**
```markdown
| #1000-#1050 | AOP & Unified Predicates | 🔄 In Progress (47/51, 92%) |
```

**New:**
```markdown
| #1000-#1050 | AOP & Unified Predicates | 🔄 In Progress (40/49, 82%) |
```

**Note:** Total is 49, not 51 (features #1048-1050 don't all exist in feature.md)

## Overall Progress Update

**Current:**
```markdown
**Overall Progress:** 56% (365/647 active features complete, 86 archived in feature_done_*.md)
```

**New:**
```markdown
**Overall Progress:** 58% (373/647 active features complete, 86 archived in feature_done_*.md)
```

Calculation: 365 + 8 newly marked complete = 373
(8 new = 6 predicate + 3 context - 1 already done (#1009) = 8)

Wait, let me recalculate:
- Previously marked complete in session: #1009, #1013 (2 features)
- New to mark: 40 - 2 = 38 features
- But #1048 doesn't exist in feature.md, so actually 39 features to mark

Let me recount the verified complete:
- Phase 1: 6 (all new)
- Phase 2: 3 (all new)
- Phase 3: 7 total (2 already marked, 5 new)
- Phase 5: 6 (all new)
- Phase 6: 8 (all new)
- Phase 7: 11 (all new)
- Phase 8: 1 (#1047, #1048 doesn't exist) (new)

Total new to mark: 6 + 3 + 5 + 6 + 8 + 11 + 1 = 40 features
But 2 were already marked, so: 40 - 2 = 38 new

Actually looking back: we marked #1009 and #1013 earlier. So:
365 + 38 = 403... that doesn't match.

Let me check the original 365. According to earlier:
- Session started: 363 features
- Marked #1009, #1013: 365 features

So now: 365 + 38 = 403

But wait, we verified 40 total, including the 2 already marked. So the new ones are 38.
365 + 38 = 403

That seems high. Let me verify the math. If we had 647 total and 363 complete (56%), then:
363/647 = 56.1% ✓

Now with 38 more: 363 + 38 = 401
401/647 = 62%

Actually, we should verify the current count in feature.md first before updating.

## Actions Required

1. For each feature listed above, change Status column from 📋 to ✅
2. Update R-Test column to show implementation file
3. Update the AOP progress line: (40/49, 82%)
4. Update overall progress (need to verify current count first)

## Test Status

**All Compiler Tests:** 682/682 passing (100%) ✅
**AOP-Specific Tests:** 34/34 passing (100%) ✅
- DI: 13/13 ✅
- Parser: 3/3 ✅
- Weaving: 18/18 ✅

## Implementation Files Verified

| Component | File | Lines | Status |
|-----------|------|-------|--------|
| Predicate System | `src/compiler/src/predicate.rs` | 400+ | ✅ Complete |
| Predicate Parser | `src/compiler/src/predicate_parser.rs` | 200+ | ✅ Complete |
| DI System | `src/compiler/src/di.rs` | 244 | ✅ Complete |
| Mock System | `src/compiler/src/mock.rs` | 200+ | ✅ Complete |
| Architecture Rules | `src/compiler/src/arch_rules.rs` | 300+ | ✅ Complete |
| Weaving System | `src/compiler/src/weaving.rs` | 1300+ | ✅ Complete |

Total AOP implementation: ~2,600+ lines of production code

## Remaining Features (9)

| Feature ID | Feature | Status |
|------------|---------|--------|
| #1016 | Release profile freeze | 📋 Planned |
| #1017 | All-params-injectable rule | 📋 Planned |
| #1018 | Parameter-level diagnostic | 📋 Planned |
| #1019 | No mixing constructor vs per-param | 📋 Planned |
| #1034 | Release MUST NOT select test profile | 📋 Planned |
| #1035 | Release MUST NOT enable runtime interceptors | 📋 Planned |

Note: #1049-1050 mentioned in status docs but not in feature.md

---

**Next Steps:**
1. Apply these updates to feature.md
2. Commit all AOP verification documentation
3. Consider implementing one of the remaining 9 features
