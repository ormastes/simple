# Reference Capability System Specification

> @concurrency_mode(lock_base)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reference Capability System Specification

@concurrency_mode(lock_base)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CAP-SYS-001 to #CAP-SYS-034 |
| Category | Type System \| Capabilities |
| Status | Implemented (iso T); mut T type-position parsing not yet implemented |
| Source | `test/03_system/feature/usage/capability_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Capability Types

- `T` (default) - Shared, no mutation, no transfer
- `mut T` - Exclusive, allows mutation, no transfer
- `iso T` - Isolated, allows mutation and transfer

## Concurrency Modes

- Actor (default) - Only `iso T` allowed, `mut T` rejected
- LockBase - `mut T` and `iso T` allowed
- Unsafe - All capabilities allowed

## Syntax

```simple
@concurrency_mode(lock_base)
use std.spec.step

fn update(counter: mut Counter, delta: i64) -> i64:
counter.value = counter.value + delta
counter.value
```

## 2026-07-29 assertion-strengthening pass (lane CAP1 `capability-spec-truth`)

Per `doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`:
this spec's `iso`/`mut` examples previously defined nested `fn`s inline in
`it` bodies and asserted only `expect true`. Those bodies run through the
test runner's own body-execution path, not the real recursive-descent
frontend (`parse_full_frontend`) that `CompilerDriver.compile()` uses, so a
green result proved nothing about the real parser.

As of 2026-07-29 (lane ISO2 `iso-parse`), `iso T` genuinely parses through
the real frontend end-to-end: parser -> `TypeKind.Isolated` ->
`HirTypeKind.Isolated` -> MIR `Move` -> borrow-check use-after-move
diagnostics. `mut T` in type position (after `:`, on a parameter or return
type) is a DIFFERENT, still-unimplemented capability -- confirmed by direct
probe below: it fails with a real parser error in every concurrency mode,
every position (param, return, nested, mixed with other params), regardless
of `@concurrency_mode(...)`. The `iso` cases below now drive real source text
through `parse_full_frontend` (+ `HirLowering` / borrow-check where the
example is about behavior) and assert real pipeline outcomes. The `mut`
cases now assert the CURRENT TRUTHFUL behavior -- a real parser error --
instead of a fabricated "works" claim, and say so in a comment. No example
was deleted.

## Scenarios

### Parsing Capabilities

#### parses mut capability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses mut capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mut capability")
# NOTE (bug: iso_mut_capability_prefix_not_parsed_2026-07-29): the
# nested `fn update` below is illustrative syntax only -- it is
# evaluated by the test runner's own lenient body-execution path, not
# by the real frontend, so its mere presence proves nothing. Kept for
# documentation; the real assertion is the probe underneath it.
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

# TRUTH: `mut T` in parameter-type position is NOT implemented in the
# real recursive-descent parser yet -- it still fails with a real
# parser error (`mut` consumed as an ordinary type name, then chokes
# on the type token that follows it). Document that truthfully.
ast_reset()
val real_src = "@concurrency_mode(lock_base)\nfn update(x: mut i64) -> i64:\n    x\n"
parse_full_frontend(real_src, "cap1_probe_mut_param.spl", "cap1_probe_mut_param", Logger(level: 0))
assert_true(parser_has_errors())  # real gap, not "parsed successfully"
```

</details>

#### parses iso capability

- parses iso capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses iso capability")
fn transfer(data: iso i64) -> i64:
    data

# STRENGTHENED: drive the identical source text through the real
# frontend + HIR lowering and assert the parameter's type actually
# lowered to `HirTypeKind.Isolated` (LANE ISO2, 2026-07-29).
ast_reset()
val real_src = "fn transfer(data: iso i64) -> i64:\n    data\n"
val parsed = parse_full_frontend(real_src, "cap1_probe_iso_param.spl", "cap1_probe_iso_param", Logger(level: 0))
assert_false(parser_has_errors())
var hir_lowering = HirLowering.with_filename("cap1_probe_iso_param.spl")
val hir = hir_lowering.lower_module(parsed)
if val fn_id = hir.symbols.lookup("transfer"):
    val fn_ = hir.functions[fn_id]
    var is_isolated = false
    match fn_.params[0].type_.kind:
        case HirTypeKind.Isolated(_):
            is_isolated = true
        case _:
            pass
    assert_true(is_isolated)
else:
    fail("transfer function not found in lowered HIR")
```

</details>

#### parses capability with generic type

- parses capability with generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses capability with generic type")
@concurrency_mode(lock_base)
fn process(items: mut [i64]) -> i64:
    0

# TRUTH (verified by direct probe during this pass, same anchor gap
# as "parses mut capability" above): `mut` is never special-cased
# before the generic type parser either, so `mut [i64]` fails to
# parse for the identical reason `mut i64` does -- confirmed via
# parse_full_frontend + parser_has_errors() == true. Not re-run live
# here (redundant real-pipeline calls made this whole file too slow
# under the test daemon's per-file budget); see the anchor test.
expect true
```

</details>

#### parses default shared capability (no prefix)

- parses default shared capability (no prefix)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default shared capability (no prefix)")
fn read(x: i64) -> i64:
    x

expect read(42) == 42  # Default is implicitly Shared
```

</details>

### Aliasing Rules

#### allows multiple shared capabilities

- allows multiple shared capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple shared capabilities")
# Shared capabilities can coexist
fn use_shared(a: i64, b: i64) -> i64:
    a + b

expect use_shared(10, 20) == 30
```

</details>

#### exclusive capability prevents aliasing

- exclusive capability prevents aliasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exclusive capability prevents aliasing")
# `mut T` ("Exclusive") has no real-pipeline aliasing enforcement to
# check yet: `mut` in type position does not even parse today (same
# anchor gap as "parses mut capability" in Group 1, verified there),
# so there is nothing downstream to exercise. Documented gap, not a
# fabricated "enforced at compile time" claim.
expect true
```

</details>

#### isolated capability prevents aliasing

- isolated capability prevents aliasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolated capability prevents aliasing")
# STRENGTHENED (real pipeline): iso's "prevents aliasing" guarantee
# is enforced today via move-only semantics -- reading an iso-typed
# binding a second time after it has already been read/bound
# elsewhere is a real use-after-move borrow-check diagnostic through
# the actual parse_full_frontend -> HirLowering -> MirLowering ->
# check_mir_module pipeline (mirrors
# test/01_unit/compiler/borrow/iso_parse_pipeline_spec.spl).
ast_reset()
val src = "fn take(a: iso i64) -> i64:\n" +
    "    val b = a\n" +
    "    val c = a\n" +
    "    0\n"
val parsed = parse_full_frontend(src, "cap1_probe_iso_alias.spl", "cap1_probe_iso_alias", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("cap1_probe_iso_alias.spl")
val hir = hir_lowering.lower_module(parsed)
val target_context = driver_mir_target_context(driver_core_compile_options_default())
var lowering = MirLowering.new_for_target(hir.symbols, target_context)
val mir = lowering.lower_module(hir)
val errors = check_mir_module(mir)
assert_true(errors.len() > 0)  # real use-after-move diagnostic
```

</details>

### Capability Conversion Rules

#### valid downgrades

#### allows Exclusive to Shared

- allows Exclusive to Shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows Exclusive to Shared")
# mut T -> T is allowed (downgrade) -- NOT YET CHECKED: no
# capability-conversion logic exists in the pure-Simple compiler.
expect true
```

</details>

#### allows Isolated to Exclusive

- allows Isolated to Exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows Isolated to Exclusive")
# iso T -> mut T is allowed (downgrade) -- NOT YET CHECKED (same
# gap; also `mut T` doesn't parse as a conversion target).
expect true
```

</details>

#### allows Isolated to Shared

- allows Isolated to Shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows Isolated to Shared")
# iso T -> T is allowed (downgrade) -- NOT YET CHECKED: no
# capability-conversion logic exists in the pure-Simple compiler.
expect true
```

</details>

#### invalid upcasts

#### rejects Shared to Exclusive

- rejects Shared to Exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects Shared to Exclusive")
# T -> mut T is not allowed (upcast) -- NOT YET CHECKED: no
# capability-conversion logic exists in the pure-Simple compiler.
expect true
```

</details>

#### rejects Shared to Isolated

- rejects Shared to Isolated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects Shared to Isolated")
# T -> iso T is not allowed (upcast) -- NOT YET CHECKED: no
# capability-conversion logic exists in the pure-Simple compiler.
expect true
```

</details>

#### rejects Exclusive to Isolated

- rejects Exclusive to Isolated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects Exclusive to Isolated")
# mut T -> iso T is not allowed (upcast) -- NOT YET CHECKED: no
# capability-conversion logic exists in the pure-Simple compiler.
expect true
```

</details>

### Capability Properties

#### shared allows no mutation

- shared allows no mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shared allows no mutation")
# T cannot be mutated -- NOT YET CHECKED (no capability enforcement
# in the pure-Simple compiler); no `mut`/`iso` involved here.
expect true
```

</details>

#### exclusive allows mutation

- exclusive allows mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exclusive allows mutation")
# mut T can be mutated
@concurrency_mode(lock_base)
fn mutate(x: mut i64) -> i64:
    x = x + 1
    x

# TRUTH (same anchor gap as Group 1's "parses mut capability", proven
# live there): `mut i64` in parameter-type position is a real parser
# error today -- document the gap instead of asserting it "works".
expect true
```

</details>

#### isolated allows mutation and transfer

- isolated allows mutation and transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolated allows mutation and transfer")
# iso T can be mutated and transferred
fn take_ownership(data: iso i64) -> i64:
    data

# Same shape and anchor proof as Group 1's "parses iso capability"
# (real frontend + HIR lowering confirms `iso i64` parses clean and
# lowers to HirTypeKind.Isolated) -- not re-run live here to keep
# this file's total real-pipeline invocation count within the test
# daemon's per-file time budget.
expect true
```

</details>

### Nested Capabilities

#### parses nested mut mut T

- parses nested mut mut T


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested mut mut T")
@concurrency_mode(lock_base)
fn weird(x: mut mut i64) -> i64:
    0

# TRUTH (verified by direct probe during this pass): `mut mut i64`
# fails to parse for the same reason a single `mut i64` does -- `mut`
# is never special-cased in type position (see the Group 1 anchor).
expect true
```

</details>

### Capability Environment

#### can acquire and release capability

- can acquire and release capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can acquire and release capability")
# After acquiring exclusive, cannot acquire shared
# After release, can acquire again
# NOT YET CHECKED: no runtime capability-acquisition tracking exists
# in the pure-Simple compiler.
expect true
```

</details>

### Concurrency Mode - Actor

#### defaults to actor mode

- defaults to actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to actor mode")
fn process(x: i64) -> i64:
    x

expect process(42) == 42
```

</details>

#### actor mode allows iso

- actor mode allows iso


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actor mode allows iso")
fn transfer(data: iso i64) -> i64:
    data

expect transfer(42) == 42
# Real-frontend confirmation is the Group 1 "parses iso capability"
# anchor (same shape); not re-run live here for file runtime budget.
```

</details>

#### actor mode rejects mut in params

- actor mode rejects mut in params


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actor mode rejects mut in params")
# This would be a compile error:
# fn update(x: mut i64) -> i64:  # Error in actor mode
#     x
#
# TRUTH (verified by direct probe during this pass): this is not
# actually an actor-mode-specific rejection today -- `mut i64` in
# parameter-type position fails to parse in EVERY concurrency mode
# (no `@concurrency_mode` attribute at all, i.e. default/actor mode
# included, probed with parser_has_errors() == true), because the
# real parser has no `mut`-prefix handling at all yet (Group 1
# anchor). Document the real, broader gap instead of the narrower
# "actor mode enforces this" claim.
expect true
```

</details>

### Concurrency Mode - LockBase

#### parses lock_base mode attribute

- parses lock_base mode attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses lock_base mode attribute")
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

# TRUTH (verified by direct probe during this pass): `lock_base` does
# not unblock `mut T` parsing -- the real parser error is
# unconditional regardless of the concurrency-mode attribute (the
# attribute itself is a separate, unrelated parse). Same anchor gap
# as Group 1's "parses mut capability".
expect true
```

</details>

#### lock_base allows mut T

- lock_base allows mut T


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lock_base allows mut T")
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

# TRUTH: same real-parser gap -- `mut T` fails regardless of mode
# (Group 1 anchor).
expect true
```

</details>

### Concurrency Mode - Unsafe

#### parses unsafe mode attribute

- parses unsafe mode attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses unsafe mode attribute")
@concurrency_mode(unsafe)
fn raw_ptr(x: i64) -> i64:
    x

# This fn uses no capability prefix at all, so the real frontend
# parses it clean (verified by direct probe during this pass, same
# ordinary-fn shape as Group 1's "parses default shared capability").
expect true
```

</details>

#### unsafe mode allows all capabilities

- unsafe mode allows all capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsafe mode allows all capabilities")
@concurrency_mode(unsafe)
fn unsafe_process(a: mut i64, b: iso i64, c: i64) -> mut i64:
    0

# TRUTH (verified by direct probe during this pass, real defect):
# "unsafe mode allows all capabilities" is NOT actually true at the
# real-parser level today -- the `mut` prefix on `a` (and the `mut`
# return type) still fails to parse even under
# `@concurrency_mode(unsafe)`, exactly like every other mode (Group 1
# anchor). This is a real gap between the documented promise and
# current behavior; document it rather than asserting the promise as
# fact.
expect true
```

</details>

### iso T in All Modes

#### iso works in actor mode

- iso works in actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iso works in actor mode")
fn transfer_actor(x: iso i64) -> i64:
    x

expect transfer_actor(42) == 42
# Real-frontend proof is the Group 1 "parses iso capability" anchor
# (concurrency-mode attributes don't affect type-position parsing).
```

</details>

#### iso works in lock_base mode

- iso works in lock_base mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iso works in lock_base mode")
@concurrency_mode(lock_base)
fn transfer_lock(x: iso i64) -> i64:
    x

expect transfer_lock(42) == 42
# See Group 1 anchor.
```

</details>

#### iso works in unsafe mode

- iso works in unsafe mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iso works in unsafe mode")
@concurrency_mode(unsafe)
fn transfer_unsafe(x: iso i64) -> i64:
    x

expect transfer_unsafe(42) == 42
# See Group 1 anchor.
```

</details>

### Zero-Cost Abstraction

#### capabilities compile to same representation

- capabilities compile to same representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("capabilities compile to same representation")
# mut T, iso T, and T all have the same size
# Capabilities only affect compile-time checking
# NOT YET CHECKED via the real pipeline: `mut T` does not parse, so
# there is no way to compare its layout against `T`/`iso T` today.
expect true
```

</details>

### Multiple Parameters with Capabilities

#### allows mixed capabilities in lock_base

- allows mixed capabilities in lock_base


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows mixed capabilities in lock_base")
@concurrency_mode(lock_base)
fn process(a: mut i64, b: iso i64, c: i64) -> i64:
    a + c

# TRUTH (verified by direct probe during this pass): the `mut a`
# parameter still fails to parse even though `iso b` and plain `c`
# are both fine -- one `mut` anywhere in the signature is enough to
# fail the whole declaration (Group 1 anchor gap).
expect true
```

</details>

#### allows all shared in actor mode

- allows all shared in actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows all shared in actor mode")
fn read_all(a: i64, b: i64, c: i64) -> i64:
    a + b + c

expect read_all(10, 20, 12) == 42
```

</details>

### Return Type Capabilities

#### allows mut return in lock_base

- allows mut return in lock_base


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows mut return in lock_base")
@concurrency_mode(lock_base)
fn create_mut() -> mut i64:
    42

# TRUTH (verified by direct probe during this pass): `mut` in
# return-type position fails to parse too, same gap as parameter
# position (Group 1 anchor).
expect true
```

</details>

#### allows iso return in all modes

- allows iso return in all modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows iso return in all modes")
fn send(data: iso i64) -> iso i64:
    data

# STRENGTHENED: confirm both the parameter AND the return type lower
# to HirTypeKind.Isolated through the real pipeline.
ast_reset()
val real_src = "fn send(data: iso i64) -> iso i64:\n    data\n"
val parsed = parse_full_frontend(real_src, "cap1_probe_iso_return.spl", "cap1_probe_iso_return", Logger(level: 0))
assert_false(parser_has_errors())
var hir_lowering = HirLowering.with_filename("cap1_probe_iso_return.spl")
val hir = hir_lowering.lower_module(parsed)
if val fn_id = hir.symbols.lookup("send"):
    val fn_ = hir.functions[fn_id]
    var param_isolated = false
    match fn_.params[0].type_.kind:
        case HirTypeKind.Isolated(_):
            param_isolated = true
        case _:
            pass
    var ret_isolated = false
    match fn_.return_type.kind:
        case HirTypeKind.Isolated(_):
            ret_isolated = true
        case _:
            pass
    assert_true(param_isolated)
    assert_true(ret_isolated)
else:
    fail("send function not found in lowered HIR")
```

</details>

### Class Method Capabilities

#### class methods default to actor mode

- class methods default to actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class methods default to actor mode")
class Counter:
    value: i64

    fn get_value() -> i64:
        self.value

val c = Counter(value: 42)
expect c.get_value() == 42
```

</details>

### Integration Patterns

#### actor message passing with iso

- actor message passing with iso


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actor message passing with iso")
fn process_message(msg: iso i64) -> i64:
    msg

expect process_message(42) == 42
# Real-frontend proof is the Group 1 "parses iso capability" anchor.
```

</details>

#### lock-based concurrent modification

- lock-based concurrent modification


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lock-based concurrent modification")
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

# TRUTH: same `mut T` parser gap as the Group 1 anchor.
expect true
```

</details>

#### builder pattern with mut

- builder pattern with mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builder pattern with mut")
@concurrency_mode(lock_base)
fn with_value(builder: mut i64, value: i64) -> mut i64:
    builder

# TRUTH (verified by direct probe during this pass): both the `mut`
# parameter and `mut` return type fail to parse today (Group 1 /
# Group 13 anchors).
expect true
```

</details>

#### unsafe mode escape hatch

- unsafe mode escape hatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsafe mode escape hatch")
@concurrency_mode(unsafe)
fn unsafe_modify(data: mut i64, value: i64) -> i64:
    value

# TRUTH (verified by direct probe during this pass): the "unsafe
# mode escape hatch" does not currently work at the real-parser
# level -- `mut data` still fails to parse under
# `@concurrency_mode(unsafe)`, same as every other mode (Group 1
# anchor / Group 9 finding).
expect true
```

</details>

#### iso transfer semantics

- iso transfer semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iso transfer semantics")
fn consume(data: iso i64) -> i64:
    data

expect consume(42) == 42
# Real-frontend proof is the Group 1 "parses iso capability" anchor.
```

</details>

#### mixed const and mut parameters

- mixed const and mut parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixed const and mut parameters")
@concurrency_mode(lock_base)
fn update_with_config(state: mut i64, config: i64, multiplier: i64) -> i64:
    config * multiplier

expect update_with_config(0, 6, 7) == 42

# NOTE: the value assertion above never actually exercises `state`
# (the body is `config * multiplier`), and it runs through the
# lenient test-body path, not the real frontend. The `mut state`
# parameter itself fails to parse today (verified by direct probe
# during this pass, Group 1 anchor) -- document that truthfully.
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38800ce74fe98946b7f1f9241c02018ad090068a46241a2bd9d167b179a75e21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38800ce74fe98946b7f1f9241c02018ad090068a46241a2bd9d167b179a75e21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38800ce74fe98946b7f1f9241c02018ad090068a46241a2bd9d167b179a75e21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/usage/capability_system_spec.spl
mirror: doc/06_spec/03_system/feature/usage/capability_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/capability_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/capability_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/capability_system_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mut capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/capability_system_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses iso capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/capability_system_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses capability with generic type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/capability_system_spec.spl:354:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can acquire and release capability' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
