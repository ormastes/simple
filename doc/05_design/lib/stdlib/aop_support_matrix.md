# AOP Support Matrix

**Status:** Authoritative  
**Date:** 2026-04-04  
**Ref:** `doc/03_plan/aop_completion_plan_2026-04-04.md`

## Supported Selectors

| Selector | Syntax | Status | Backend |
|----------|--------|--------|---------|
| `execution` | `execution(* fn_name(..))` | **Supported** | Compile-time |
| `within` | `within(module.path.*)` | **Supported** | Compile-time |
| `attr` | `attr(annotation_name)` | **Supported** | Compile-time |
| `get` | `get(field)` | Deferred | — |
| `set` | `set(field)` | Deferred | — |
| `init` | `init(Type)` | Deferred | — |
| `effect` | `effect(name)` | Deferred | — |

## Supported Advice Kinds

| Advice | Syntax | When It Runs | May Change Flow |
|--------|--------|-------------|-----------------|
| `before` | `on pc{...} use handler before` | Before target | No |
| `after_success` | `on pc{...} use handler after_success` | After target returns normally | No |
| `after_error` | `on pc{...} use handler after_error` | After target raises error | No |
| `around` | `on pc{...} use handler around` | Wraps target | Yes (via proceed) |

### Around Advice Proceed Contract

- `proceed()` must be called **exactly once** per around advice invocation
- Zero calls → `ProceedError.NeverCalled`
- Multiple calls → `ProceedError.CalledMultipleTimes`
- Around advice may inspect and rewrite both return values and errors

## Supported Join Points

| Join Point | Detection | Description |
|------------|-----------|-------------|
| Execution | Function entry | Function/method call entry points |
| Decision | Branch instructions | `if`/`match` branch points |
| Condition | Comparison ops | `==`, `!=`, `<`, `>`, `<=`, `>=` |
| Error | Error blocks | Error handling / unwrap paths |
| SecurityGate | `cap=`/`resource=` attrs | Security-dimension only (Phase 7) |

## Pointcut Operators

| Operator | Syntax | Example |
|----------|--------|---------|
| AND | `&` | `execution(* foo(..)) & attr(logged)` |
| OR | `\|` | `execution(* a(..)) \| execution(* b(..))` |
| NOT | `!` | `!execution(* skip(..))` |
| Grouping | `(...)` | `(execution(*) \| within(svc.*)) & attr(tx)` |

## Weaving Backends

| Backend | Status | Default | Description |
|---------|--------|---------|-------------|
| Compile-time | **Supported** | Yes | MIR-level advice insertion during compilation |
| Runtime | **Scoped** | No | Explicit opt-in via `aop_runtime_enabled`, allowlist-gated |
| Link-time | Deferred | No | Outside completion milestone |

### Zero-Overhead Guarantee

When no aspects are defined or AOP is disabled:
- No weaving metadata emitted
- No runtime probes or proxies inserted
- Compiled output identical to non-AOP build

## Deterministic Ordering

Advice execution order is resolved by:
1. **Priority** (descending — higher number runs first for `before`, last for `after`)
2. **Specificity** (wildcard=0, glob=1, @attr=2, module=3, exact_name=4)
3. **Lexicographic** on advice function name (stable tiebreaker)

Conflicting advice (same predicate + form + priority) emits `E1504`.

## Architecture Rules

| Keyword | Purpose | Example |
|---------|---------|---------|
| `forbid` | Reject matching dependencies | `forbid pc{ import(internal.*) } "internal API"` |
| `allow` | Exception to forbid rules | `allow pc{ depend(shared.utils) } "shared OK"` |

## Error Codes

| Code | Name | Trigger |
|------|------|---------|
| E1501 | INVALID_POINTCUT_SYNTAX | Malformed `pc{...}` expression |
| E1502 | UNDEFINED_JOINPOINT | Join point not found at weave site |
| E1503 | INVALID_ADVICE_TYPE | Advice form not in supported set |
| E1504 | CONFLICTING_ADVICE_ORDER | Same predicate + form + priority |
| E1505 | INVALID_WEAVING_TARGET | Target cannot be woven (e.g., extern fn) |
| E1506 | ASPECT_CIRCULAR_DEPENDENCY | Circular around advice chain |
| E1507 | INVALID_POINTCUT_SELECTOR | Unsupported selector (get, set, init, effect) |
| E1508 | ASPECT_NOT_ENABLED | AOP referenced but not enabled |

## Verification Constraints

- Verified code rejects non-ghost aspects
- Wildcard restrictions enforced in verified pointcuts
- Security-AOP uses only supported join points and advice forms
