# F# Computation Expressions + Erlang/OTP — Implementation Plan

**Date:** 2026-02-18
**Status:** ✅ COMPLETE — Implemented 2026-02-18
**Companion research:** [`doc/research/missing_language_features_2026-02-17.md`](../research/missing_language_features_2026-02-17.md)

---

## Executive Summary

This document is an actionable implementation plan for two related feature clusters in Simple:

1. **F# Computation Expressions (CEs)** — named monadic builder blocks that desugar `bind`, `yield`, `return` inside a named `ce NAME:` block into builder method calls. The primary motivation is ergonomic `result do:` / `option do:` chaining with early-return on error.

2. **Erlang/OTP concurrency primitives** — `receive:` block for actor mailbox receive, typed `Mailbox<T>`, `monitor`/`link` process monitoring, and OTP behaviour traits (GenServer, GenStatem, GenEvent).

Both clusters build on a solid existing foundation and require careful but bounded parser work, followed by library additions. Neither requires changes to the type system or generics.

---

## Status: What Already Exists

### Parser / AST Foundation (verified in `src/compiler_core/`)

| Feature | Token | AST Tag | File | Status |
|---------|-------|---------|------|--------|
| `spawn` keyword | TOK_KW_SPAWN = 197 | EXPR_SPAWN = 39 | `ast.spl` | Done |
| `async` keyword | TOK_KW_ASYNC = 53 | EXPR_ASYNC_BLOCK = 42 | `tokens.spl` | Done |
| `await` keyword | TOK_KW_AWAIT = 54 | EXPR_AWAIT = 37 | `ast.spl` | Done |
| `yield` keyword | TOK_KW_YIELD = 37 | EXPR_YIELD = 38 | `ast.spl` | Done |
| `do:` block expr | TOK_KW_DO = 195 | EXPR_DO_BLOCK = 44 | `ast.spl` | Done |
| backtick atoms | TOK_BACKTICK_IDENT = 193 | EXPR_ATOM = 45 | `ast.spl` | Done |
| `errdefer` in lexer | TOK_KW_ERRDEFER = 187 | STMT_ERRDEFER = 15 | `ast.spl` | Partial (parsed; runtime gives "function not found") |
| Labeled loops | TOK_LABEL = 192 | — | `ast.spl` | Done |
| `defer` statement | TOK_KW_DEFER = 186 | STMT_DEFER = 14 | `ast.spl` | Done |

**Next available token slot:** 204+ (TOK_KW_MIXIN = 203 is current highest).

### Standard Library (verified in `src/std/`)

| Library | File | Status |
|---------|------|--------|
| Supervision trees | `src/std/supervisor.spl` | Done — SupervisorConfig, ChildSpec, STRATEGY_*, RESTART_*, Supervisor class |
| Result chaining | `src/std/result.spl` | Done — result_map, result_and_then, result_or_else, result_unwrap_or |
| Trait system stubs | `src/std/traits.spl` | Stubs — field_names, has_field (return placeholders pending @traits built-in) |
| Option type | `src/std/option.spl` | Done |
| Phantom types | `src/std/phantom.spl` | Done |

---

## Part 1: F# Computation Expressions

### What F# CEs Provide

Named monadic builder blocks that desugar `let!`, `yield!`, `return!` into builder method calls. Common F# CEs: `async {}`, `result {}`, `seq {}`.

### Simple Equivalents and Gaps

| F# CE | Simple equivalent | Status |
|-------|-------------------|--------|
| `async {}` block | `async fn` + `await` | Achievable now |
| `seq {}` generator | `yield` keyword | Achievable now |
| `result {}` early-return block | No direct equivalent | **Missing** |
| User-defined CE builders | No dispatch mechanism | **Missing** |

**The key missing piece** is a `bind x = expr` statement form (monadic bind inside a block) and a named CE builder dispatch mechanism (`ce result:` block desugars to builder calls).

### Proposed Syntax

**`bind` statement — monadic bind inside CE blocks:**
```simple
ce result:
    bind text_content = file_read(path)
    bind parsed = parse_config(text_content)
    Ok(parsed)
```
This desugars to:
```simple
result_builder.bind(file_read(path), fn(text_content):
    result_builder.bind(parse_config(text_content), fn(parsed):
        result_builder.return_ce(Ok(parsed))
    )
)
```

**Named CE block — `ce NAME: body`:**
```simple
val config = ce result:
    bind raw = file_read("config.sdn")
    bind parsed = sdn_parse(raw)
    bind validated = validate_config(parsed)
    Ok(validated)
```

**Shortcut form — `IDENT do:` if IDENT registered as CE builder:**
```simple
val config = result do:
    bind raw = file_read("config.sdn")
    bind parsed = sdn_parse(raw)
    Ok(parsed)
```

### Grammar Analysis for CE Features

| Feature | Grammar status | Token | Notes |
|---------|---------------|-------|-------|
| `bind x = expr` statement | ✅ Clean | TOK_KW_BIND = 204 | New keyword; `bind IDENT =` is unambiguous O(1) |
| `ce NAME:` block | ✅ Clean | TOK_KW_CE = 205 | `ce` + IDENT + `:` at stmt level; no conflict |
| `yield expr` inside CE | Already works | TOK_KW_YIELD = 37 | Existing token |
| `return expr` inside CE | Already works | TOK_KW_RETURN = 49 | Existing token |

The `bind` keyword has zero conflict risk: `bind` is not currently a keyword, and `bind IDENT = expr` is unambiguous in O(1) since no other statement begins with `bind IDENT =`.

The `ce` keyword is similarly clean: `ce` followed by an `IDENT` then `:` uniquely identifies a CE invocation block at the statement level.

---

## Part 2: Erlang/OTP Concurrency

### What Is Already Done

- `spawn` keyword and AST — actors can be spawned
- `src/std/supervisor.spl` — full supervision tree library: `one_for_one`, `one_for_all`, `rest_for_one`, `simple_one_for_one` strategies; `ChildSpec`; restart policies (permanent, temporary, transient); `Supervisor` class with `add_child`, `remove_child`, `record_restart`, `within_limits`

### What Is Not Done

| Feature | Category | Notes |
|---------|----------|-------|
| `receive:` block | Parser + eval | Core Erlang pattern; not in lexer/parser |
| `Mailbox<T>` type | Library | Typed per-actor message queue; generics work in type position |
| `monitor()` / `link()` | Library | Process monitoring as messages; library-level |
| OTP Behaviours | Library | GenServer/GenStatem/GenEvent as traits with defaults |
| Distribution primitives | Runtime/FFI | `node.send(msg)`, cluster addressing; out of scope |
| Hot code reload | Build system | Out of scope for parser-level work |

### `receive:` Block — Grammar Analysis

The `receive:` block is the core Erlang pattern. It follows match-arm syntax with an optional `after TIMEOUT:` arm:

```simple
receive:
    `ok data: handle_ok(data)
    `error msg: log_error(msg)
    after 5000: handle_timeout()
```

**Grammar:**
```
receive_stmt := 'receive' ':' NEWLINE INDENT
                  (pattern ':' body)*
                  ('after' timeout_expr ':' body)?
               DEDENT
```

This is identical to `match:` arms but with an optional `after TIMEOUT:` arm appended. Unambiguous O(1): `receive` is a new keyword; `after` is a new keyword valid inside `receive:` blocks (contextual — treated as identifier elsewhere).

**Backtick atoms are immediately useful here** — they provide Erlang-style message tags with compile-time-fixed intern sets:
```simple
receive:
    `ping sender: send_msg(sender, `pong)
    `stop: self.running = false
    after 1000: health_check()
```

### Full Grammar Analysis Table

| Feature | Grammar status | Token | Notes |
|---------|---------------|-------|-------|
| `receive:` block | ✅ Clean | TOK_KW_RECEIVE = 206 | New keyword; like `match:` + optional `after` arm |
| `after N:` arm inside receive | ✅ Clean | TOK_KW_AFTER = 207 | Contextual keyword inside `receive:` |
| `Mailbox<T>` type | ✅ Clean (existing generics) | — | Library type; no parser change needed |
| `monitor(x)` / `link(x)` | ✅ Clean | — | Library functions; no parser change |
| `@behaviour(GenServer)` | ✅ Clean | `@IDENT` existing | Uses existing annotation syntax; no new keyword |
| Distribution `node!send` | ⚠️ Non-trivial | — | Runtime FFI concern; out of scope |

---

## Token Numbering Plan

Current highest: `TOK_KW_MIXIN = 203`

| Token | Value | Purpose |
|-------|-------|---------|
| TOK_KW_BIND | 204 | `bind x = expr` monadic bind in CE blocks |
| TOK_KW_CE | 205 | `ce NAME:` named computation expression block |
| TOK_KW_RECEIVE | 206 | `receive:` Erlang mailbox receive block |
| TOK_KW_AFTER | 207 | `after TIMEOUT:` timeout arm inside `receive:` |

These follow the `200+` keyword range convention consistent with `src/compiler_core/tokens.spl`.

## AST Node Plan

Current highest STMT tag: `STMT_STATIC_FOR = 17` (inferred from existing STMT_ERRDEFER = 15, STMT_DEFER = 14)

| Node | Type | Value | Purpose |
|------|------|-------|---------|
| STMT_RECEIVE | STMT | 18 | `receive:` block statement |
| STMT_BIND | STMT | 19 | `bind x = expr` monadic bind statement |
| DECL_CE | DECL | 11 | `ce NAME:` computation expression invocation |

---

## Implementation Phases

### Phase 1 — Parser Level (lexer + parser + AST)

**Priority:** HIGH — enables all downstream work

**Files to modify:**
- `src/compiler_core/tokens.spl` — add TOK_KW_BIND (204), TOK_KW_CE (205), TOK_KW_RECEIVE (206), TOK_KW_AFTER (207)
- `src/compiler_core/lexer.spl` — add keyword recognition for `bind`, `ce`, `receive`, `after`
- `src/compiler_core/ast.spl` — add STMT_RECEIVE = 18, STMT_BIND = 19, DECL_CE = 11
- `src/compiler_core/parser.spl` — add productions for `receive:`, `bind x = expr`, `ce NAME:`
- `src/compiler_core/entity/token/kinds.spl` — sync new token constants

**Parser production for `receive:`:**
```
# receive_stmt: like match_stmt, with optional 'after' arm at end
parse_receive_stmt():
    consume TOK_KW_RECEIVE
    consume ':'
    consume NEWLINE + INDENT
    arms = []
    while peek() != TOK_KW_AFTER and peek() != TOK_DEDENT:
        arms.push(parse_match_arm())
    timeout_expr = nil
    timeout_body = nil
    if peek() == TOK_KW_AFTER:
        consume TOK_KW_AFTER
        timeout_expr = parse_expr()
        consume ':'
        timeout_body = parse_body()
    consume DEDENT
    STMT_RECEIVE(arms, timeout_expr, timeout_body)
```

**Parser production for `bind x = expr`:**
```
parse_bind_stmt():
    consume TOK_KW_BIND
    name = consume TOK_IDENT
    consume '='
    expr = parse_expr()
    STMT_BIND(name, expr)
```

**Parser production for `ce NAME:`:**
```
parse_ce_block():
    consume TOK_KW_CE
    builder_name = consume TOK_IDENT
    consume ':'
    body = parse_body()   # body may contain bind stmts, yield, return
    DECL_CE(builder_name, body)
```

**Tests to create:**
- `test/unit/compiler_core/receive_spec.spl` — receive parsing, after arm, timeout variants
- `test/unit/compiler_core/bind_stmt_spec.spl` — bind statement parsing, CE context
- `test/unit/compiler_core/ce_block_spec.spl` — named CE block parsing, desugaring output

### Phase 2 — Mailbox + Monitor Library

**Priority:** HIGH — core concurrency primitive

**Files to create:**
- `src/std/mailbox.spl` — Mailbox struct, `mailbox_new(capacity)`, `mailbox_send()`, `mailbox_receive()`, `mailbox_try_receive()`
- `src/std/monitor.spl` — `monitor()`, `link()`, DownEvent struct, LinkExitEvent struct

**Mailbox API sketch:**
```simple
# src/std/mailbox.spl
struct Mailbox:
    capacity: i64
    messages: [text]   # serialized messages (capacity-bounded)
    count: i64

fn mailbox_new(capacity: i64) -> Mailbox:
    Mailbox(capacity: capacity, messages: [], count: 0)

fn mailbox_send(mb: Mailbox, msg: text) -> bool:
    if mb.count >= mb.capacity:
        return false   # bounded — returns false on full
    mb.messages.push(msg)
    mb.count = mb.count + 1
    true

fn mailbox_receive(mb: Mailbox) -> text:
    if mb.count == 0:
        return nil
    val msg = mb.messages[0]
    mb.count = mb.count - 1
    msg
```

**Monitor API sketch:**
```simple
# src/std/monitor.spl
struct DownEvent:
    pid: i64
    reason: text

struct LinkExitEvent:
    pid: i64
    reason: text

fn monitor(pid: i64) -> i64:
    0   # Returns monitor ref id; runtime FFI stub

fn link(pid: i64):
    pass_do_nothing   # Runtime FFI stub
```

**Test symlinks to create** in `test/lib/std/`:
- `mailbox.spl` → `../../../src/std/mailbox.spl`
- `monitor.spl` → `../../../src/std/monitor.spl`

**Tests to create:**
- `test/unit/std/mailbox_spec.spl` — send/receive, capacity bounds, empty receive
- `test/unit/std/monitor_spec.spl` — monitor creation, DownEvent struct

### Phase 3 — OTP Behaviour Traits

**Priority:** MEDIUM — structured process patterns

**Files to create:**
- `src/std/gen_server.spl` — GenServer trait with default `handle_info`, `terminate`
- `src/std/gen_statem.spl` — GenStatem trait (`callback_mode`, `handle_event`, `init`, `terminate`)
- `src/std/gen_event.spl` — GenEvent trait (`add_handler`, `handle_event`, `notify`)

**GenServer trait sketch:**
```simple
# src/std/gen_server.spl
trait GenServer:
    fn init(args: text) -> text       # required — return initial state

    fn handle_call(request: text, state: text) -> text   # required

    fn handle_cast(msg: text, state: text) -> text       # required

    fn handle_info(msg: text, state: text) -> text:      # default: ignore
        state

    fn terminate(reason: text, state: text):             # default: no-op
        pass_do_nothing
```

**`@behaviour` annotation pattern** — uses existing `@IDENT` syntax, no new keyword:
```simple
@behaviour(GenServer)
class MyServer:
    state: text

    fn init(args: text) -> text:
        "idle"

    fn handle_call(request: text, state: text) -> text:
        if request == "ping": "pong"
        else: state

    fn handle_cast(msg: text, state: text) -> text:
        msg
```

**Test symlinks to create** in `test/lib/std/`:
- `gen_server.spl` → `../../../src/std/gen_server.spl`
- `gen_statem.spl` → `../../../src/std/gen_statem.spl`

**Tests to create:**
- `test/unit/std/gen_server_spec.spl` — trait method dispatch, default handle_info, terminate
- `test/unit/std/gen_statem_spec.spl` — state transitions, event dispatch

### Phase 4 — Computation Expression Protocol

**Priority:** MEDIUM — ergonomic Result/Option chaining

**Files to create:**
- `src/std/computation.spl` — CE builder trait: `bind()`, `return_ce()`, `yield_ce()`, `zero()`
- `src/std/result_ce.spl` — ResultCE: short-circuit on nil (error)
- `src/std/option_ce.spl` — OptionCE: short-circuit on nil (None)
- `src/std/seq_ce.spl` — SeqCE: sequence/generator computation expression

**CE builder protocol:**
```simple
# src/std/computation.spl
trait CeBuilder:
    fn bind(value, continuation: fn())   # monadic bind
    fn return_ce(value)                  # wrap value in context
    fn yield_ce(value)                   # default: pass_do_nothing
    fn zero()                            # default empty/failed value
```

**ResultCE builder:**
```simple
# src/std/result_ce.spl
fn result_ce_bind(value, continuation: fn()):
    if value == nil:
        return nil   # short-circuit on error
    continuation(value)

fn result_ce_return(value):
    value

fn result_ce_zero():
    nil
```

**Desugaring example:**
```simple
# Source:
val config = ce result:
    bind raw = file_read("config.sdn")
    bind parsed = sdn_parse(raw)
    Ok(parsed)

# Desugared by eval pass:
val config = result_ce_bind(file_read("config.sdn"), fn(raw):
    result_ce_bind(sdn_parse(raw), fn(parsed):
        result_ce_return(Ok(parsed))
    )
)
```

**Tests to create:**
- `test/unit/std/result_ce_spec.spl` — bind propagation, early return on nil
- `test/unit/std/option_ce_spec.spl` — bind propagation, early return on nil

### Phase 5 — Eval/Interpreter Support

**Priority:** MEDIUM — makes `receive:` and `ce:` actually execute

**Files to modify:**
- `src/compiler_core/interpreter/eval.spl` — add handlers for STMT_RECEIVE, STMT_BIND; CE desugaring pass
- `src/compiler_core/entity/token/kinds.spl` — add new token constants

**`receive:` eval sketch:**
```simple
# Inside eval_stmt() — handle STMT_RECEIVE
fn eval_receive_stmt(stmt_idx: i64, env: i64):
    val mb = env_get_mailbox(env)
    # Try to match each arm against next queued message
    val arms = stmt_body_list(stmt_idx)
    var matched = false
    var result = unit_value()
    for arm in arms:
        val msg = mailbox_try_receive(mb)
        if msg != nil:
            val m = try_match_pattern(arm_pattern(arm), msg, env)
            if m != nil:
                result = eval_stmts(arm_body(arm), m)
                matched = true
                break
    # After arm if no match
    if not matched:
        val timeout_body = stmt_alt_body(stmt_idx)
        if timeout_body >= 0:
            result = eval_stmts(timeout_body, env)
    result
```

**`bind` eval sketch (inside ce block):**
```simple
# STMT_BIND: eval rhs, bind to name in env, continue
fn eval_bind_stmt(stmt_idx: i64, env: i64, builder_name: text):
    val rhs = eval_expr(stmt_expr(stmt_idx), env)
    # Look up builder's bind function
    val bind_fn_name = "{builder_name}_ce_bind"
    # The CE desugar pass converts the remaining stmts into a continuation lambda
    # and calls bind_fn_name(rhs, continuation)
    rhs   # simplified — full impl uses continuation-passing transform
```

---

## Code Examples: Complete Feature Showcase

### F# CE — Result Chaining

```simple
use std.result_ce.{result_ce_bind, result_ce_return}

fn load_user_config(user_id: i64) -> text:
    ce result:
        bind profile = fetch_profile(user_id)
        bind prefs = load_preferences(profile.id)
        bind validated = validate_prefs(prefs)
        Ok(validated.to_text())
```

### F# CE — Sequence Generator

```simple
fn even_numbers(limit: i64) -> [i64]:
    ce seq:
        bind n = range(0, limit)
        if n % 2 == 0:
            yield n
```

### Erlang/OTP — receive: block with atoms

```simple
fn message_loop():
    receive:
        `ping sender: send_msg(sender, `pong)
        `work data:
            val result = process(data)
            reply(result)
        `stop: return
        after 30000:
            heartbeat()
            message_loop()
```

### Erlang/OTP — GenServer behaviour

```simple
@behaviour(GenServer)
class CounterServer:
    count: i64

    fn init(args: text) -> text:
        "0"

    fn handle_call(request: text, state: text) -> text:
        if request == "get": state
        elif request == "inc":
            val n = int(state)
            "{n + 1}"
        else: state

    fn handle_cast(msg: text, state: text) -> text:
        state

fn run_counter():
    val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
    sup.add_child(child_spec("counter"))
    sup.start()
```

### Erlang/OTP — Bounded mailbox

```simple
use std.mailbox.{mailbox_new, mailbox_send, mailbox_receive}

fn worker_loop(mb: Mailbox):
    val msg = mailbox_receive(mb)
    if msg != nil:
        process_message(msg)
        worker_loop(mb)

val mb = mailbox_new(100)   # bounded: max 100 messages
mailbox_send(mb, "hello")
```

---

## Safety Profile Notes

All new features respect the JSF AV C++ / NASA Power of Ten constraints from `doc/research/missing_language_features_2026-02-17.md`.

| Feature | Safety Profile | Constraint |
|---------|---------------|------------|
| `receive:` block | Conditional | In safety profile: `after TIMEOUT:` arm is **required** — no indefinite blocking |
| `bind x = expr` | ✅ Safe | Pure desugaring; no hidden allocation |
| `ce NAME:` block | Conditional | Must be total/terminating; step limits enforced |
| `Mailbox<T>` | Conditional | `capacity:` parameter required; no auto-grow; `send` returns bool |
| `monitor()` / `link()` | ✅ Safe | Observational monitoring; structured exit propagation |
| GenServer/GenStatem | ✅ Safe | Explicit state types; no hidden global state |
| Supervision trees | Already constrained | `SupervisorConfig.max_restarts` + `max_seconds` already in `supervisor.spl` |

### Key Safety Rules

- **`receive:` with `after`:** In `--profile=safety`, omitting `after TIMEOUT:` is a compiler error. Prevents indefinite blocking.
- **Mailbox:** `mailbox_new(capacity: N)` with fixed `N` is the only form. No auto-grow. `mailbox_send` returns `bool` — callers must handle queue-full.
- **CE blocks:** Inside `ce result:`, bind chains are bounded by the static number of `bind` statements. No unbounded recursion introduced.
- **Supervision:** `SupervisorConfig.max_restarts` is already a required field. Restart budgets are not optional.
- **OTP behaviours:** Default `handle_info` discards unknown messages — conservative and safe. Default `terminate` is a no-op.

---

## Out of Scope

- **Hot code reload** — compiler/build system; future work
- **Distribution primitives** — runtime FFI; `node.send(msg)`, cluster addressing
- **Selective receive** — complexity/safety concern; initial version uses FIFO-only
- **OTP Applications/Releases** — build system concern
- **Phantom types** — separate research in `doc/research/introspection_phantom_types_2026-02-17.md`
- **Mapped types** — separate feature; `doc/research/missing_language_features_2026-02-17.md` section 30

---

## File Summary

### Files to Create

| File | Phase | Purpose |
|------|-------|---------|
| `src/std/mailbox.spl` | 2 | Bounded typed message queue |
| `src/std/monitor.spl` | 2 | monitor(), link(), DownEvent, LinkExitEvent |
| `src/std/gen_server.spl` | 3 | GenServer OTP behaviour trait |
| `src/std/gen_statem.spl` | 3 | GenStatem OTP behaviour trait |
| `src/std/gen_event.spl` | 3 | GenEvent OTP behaviour trait |
| `src/std/computation.spl` | 4 | CE builder trait |
| `src/std/result_ce.spl` | 4 | ResultCE builder (Result monad) |
| `src/std/option_ce.spl` | 4 | OptionCE builder (Option monad) |
| `src/std/seq_ce.spl` | 4 | SeqCE builder (sequence/generator) |
| `test/unit/compiler_core/receive_spec.spl` | 1 | receive: parser tests |
| `test/unit/compiler_core/bind_stmt_spec.spl` | 1 | bind statement parser tests |
| `test/unit/compiler_core/ce_block_spec.spl` | 1 | ce NAME: parser tests |
| `test/unit/std/mailbox_spec.spl` | 2 | Mailbox library tests |
| `test/unit/std/monitor_spec.spl` | 2 | Monitor library tests |
| `test/unit/std/gen_server_spec.spl` | 3 | GenServer behaviour tests |
| `test/unit/std/gen_statem_spec.spl` | 3 | GenStatem behaviour tests |
| `test/unit/std/result_ce_spec.spl` | 4 | ResultCE tests |
| `test/unit/std/option_ce_spec.spl` | 4 | OptionCE tests |

### Files to Modify

| File | Phase | Change |
|------|-------|--------|
| `src/compiler_core/tokens.spl` | 1 | Add TOK_KW_BIND=204, TOK_KW_CE=205, TOK_KW_RECEIVE=206, TOK_KW_AFTER=207 |
| `src/compiler_core/lexer.spl` | 1 | Recognize `bind`, `ce`, `receive`, `after` as keywords |
| `src/compiler_core/ast.spl` | 1 | Add STMT_RECEIVE=18, STMT_BIND=19, DECL_CE=11 |
| `src/compiler_core/parser.spl` | 1 | Add productions for receive:, bind x = expr, ce NAME: |
| `src/compiler_core/interpreter/eval.spl` | 5 | Handlers for STMT_RECEIVE, STMT_BIND, DECL_CE desugaring |
| `src/compiler_core/entity/token/kinds.spl` | 5 | Sync new token constants |

---

## Connection to Existing Research

This plan directly implements:
- `doc/research/missing_language_features_2026-02-17.md` **section 15** (Process Supervision Trees) — extended with `receive:` block (the missing core Erlang primitive)
- **Section 13** (Result/Option ergonomics) — CEs provide the structured monadic layer above the chaining methods already in `src/std/result.spl`

The safety profile notes are consistent with the baseline constraints in the research doc's safety profile section.

---

## Next Steps (Checklist)

- [x] Phase 1: Add four new tokens to `src/compiler_core/tokens.spl`
- [x] Phase 1: Update `src/compiler_core/lexer.spl` keyword table
- [x] Phase 1: Add STMT_RECEIVE, STMT_BIND, DECL_CE to `src/compiler_core/ast.spl`
- [x] Phase 1: Add parser productions for `receive:`, `bind`, `ce NAME:`
- [x] Phase 1: Write tests — receive_spec, bind_stmt_spec, ce_block_spec
- [x] Phase 2: Implement `src/std/mailbox.spl` + tests
- [x] Phase 2: Implement `src/std/monitor.spl` + tests
- [x] Phase 3: Implement `src/std/gen_server.spl`, `gen_statem.spl`, `gen_event.spl` + tests
- [x] Phase 4: Implement CE builder protocol + result_ce, option_ce, seq_ce
- [x] Phase 5: Add eval handlers in `src/compiler_core/interpreter/eval.spl`
- [x] Phase 5: Sync `src/compiler_core/entity/token/kinds.spl`
- [x] Run full test suite after each phase — zero regressions required
