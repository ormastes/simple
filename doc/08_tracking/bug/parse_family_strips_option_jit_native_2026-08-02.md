# BUG: the `parse_*` text-method family silently strips the Option on JIT and native

## 2026-08-17 (batch_02 core-silent-wrong lane): reproduced, and the "absence → 0"
## half shares ONE root cause with `seed_interp_option_match_falls_through_at_scale`

Reproduced on a seed freshly built from `88227f48202` (so this is not the
stale-deployed-binary artefact that closed three sibling docs today):

```
val bad = "zz".parse_int()
print(bad ?? -1)      # JIT: 0     interpreter: -1
```

**Mode 1 ("absence → 0") is not a `parse_*` alias-table problem at all.** It is
the general presence test. `rt_is_none`
(`src/compiler_rust/runtime/src/value/objects.rs`) opened with

```rust
if value.0 == 0 || value.0 == TAG_SPECIAL { return true; }
```

and integers box as `(v << 3) | TAG_INT` with `TAG_INT = 0b000`, so the integer
**0 boxes to the bit pattern `0x0`** — bit-identical to that "raw nil" test. Any
raw 0 reaching a `T?` slot therefore reads as absent, whatever produced it. The
same line makes a genuinely present `Some(0)` read as absent, which is the
separately-filed
`doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md`
— the two docs are opposite directions of one collision.

Fixed by dropping both raw comparisons (`is_nil()` already tests the canonical
sentinel `3`). Pinned by
`test/01_unit/compiler/codegen/probe_option_presence_falsy_payload.spl` and its
two specs, whose `parse_fail_default` / `parse_ok_zero` rows are exactly this
doc's mode 1.

**Mode 2 ("present 3 → absent") did NOT reproduce** — `"3".parse_int() ?? -1`
returned `3` correctly on both engines, before and after. Either it was fixed
separately or it was always specific to a shape not captured by the doc's own
example. The per-method return-shape table (`parse_i64` unmapped, etc.) was NOT
re-measured here and remains open on its own merits; only the value-level
"failed parse is indistinguishable from 0" claim is closed.

- **Status:** OPEN — measured, staged migration designed, stage 0 (measurement) landed
- **Filed:** 2026-08-02
- **Base sha measured:** `a788a2a3e5c68ef1736401428397b5bf950d3a67`
- **Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`, enum-probe = 0 ⇒ **Rust seed**
  (`strings <bin> | grep -c "enum construction: unregistered enum"`)
- **Engine knob:** `SIMPLE_EXECUTION_MODE`. Native column via `compile --native` + running the ELF.
- Supersedes two prior lane declines that correctly refused to ship `parse_i64` alone,
  because the scope is a family and not a symbol.

## 1. Summary

`text.parse_int()` and its siblings return an **`Option`** in the interpreter and
a **raw scalar** under the JIT and native backends. The Option is discarded by
the codegen alias tables, which map the whole family onto the total,
never-failing `rt_string_to_int` / `rt_string_to_float` entry points.

Two distinct silent-wrong-answer modes follow, and **both are proved at value
level below**:

- **Absence → 0.** A failed parse is indistinguishable from a successful parse
  of `"0"`.
- **Present 3 → absent.** A *successful* parse of `"3"` is reported as absent by
  `??`, because the raw `i64` 3 lands unboxed in a declared `T?` slot and the nil
  sentinel *is* the integer 3.

The second mode is the more dangerous one and is invisible to any probe whose
correct answer is not exactly 3.

## 2. The family, enumerated, with per-engine return shape

Enumeration is exhaustive over the codegen alias tables and the interpreter
method table; the family is closed at six names.

| method | interpreter | JIT | native (`compile --native`) |
|---|---|---|---|
| `parse_int` | `Option<i64>` — `Value::some` / `Value::none` | raw `i64` via `rt_string_to_int`, **0 on failure** | same alias, **0 on failure** |
| `parse_i64` | `Option<i64>` | **not mapped at all** — `Function 'str.parse_i64' not found` on stderr, expression evaluates to garbage **27**, process **exit 0** | not in `mangle.rs` allow-list |
| `parse_i32` | `Option<i64>` | **not mapped at all** — same failure shape | not in `mangle.rs` allow-list |
| `parse_float` | `Option<f64>` | raw via `rt_string_to_float` (returns `NIL` on failure, but `??` does not fire) | as JIT |
| `parse_f64` | `Option<f64>` | as `parse_float` | as JIT |
| `parse_f64_safe` | `Option<f64>` | as `parse_float` | as JIT |

Sites (all PROVED by reading, marked as static evidence):

- interpreter: `src/compiler_rust/compiler/src/interpreter_method/string.rs:344,350`
- HIR types: `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:1179` (`TypeId::I64`), `:1385` (`TypeId::ANY`)
- alias tables (six, must be changed together — a sweep that misses one leaves a sibling):
  - `src/compiler_rust/compiler/src/codegen/instr/calls.rs:2817,3261`
  - `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1487`
  - `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:1942,2105`
  - `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2394`
  - `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:200`
  - `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:939-944`

`to_int` / `to_i64` / `to_float` / `to_f64` are **not** part of this family. They
are documented as total, 0-on-failure conversions and must keep that behaviour.

### 2b. Runtime-level semantic divergence between the two runtimes

Recorded rather than silently resolved:

- Rust `simple-runtime` `rt_string_to_int` (`runtime/src/value/collections.rs:2741`)
  is **strict** whole-string `str::parse::<i64>()` ⇒ `"4.2"` → 0.
- C `runtime_native.c:3635` `rt_string_to_int` is **`strtoll`**, a lenient
  leading-prefix parse ⇒ `"4.2"` → 4.

The two runtimes therefore disagree on the same symbol name. Measured native
output below follows the **strict** semantics.

## 3. Value-level evidence

Interpreter is the reference oracle; expectations are hand-computed, not taken
from cross-engine agreement. `"0"` and `"3"` are carried as **deliberate
controls** because 0 and 3 are exactly the values that cannot discriminate.

Probe: `print(label + (s.parse_int() ?? -99).to_text())`, sentinel `-99` chosen
outside {0, 3, nil}.

| input | interpreter (correct) | JIT | verdict |
|---|---|---|---|
| `"42"` | 42 | 42 | agree |
| `"abc"` | **-99** (None) | **0** | JIT silent wrong — absence became 0 |
| `"0"` | 0 | 0 | **control** — JIT accidentally right, cannot discriminate |
| `"3"` | 3 | **-99** | **JIT silent wrong the other way — a present 3 read as absent** |
| `"4.2"` | **-99** (None) | **0** | JIT silent wrong |
| `"  42  "` | 42 | 42 | agree — both trim |
| `"-5"` | -5 | -5 | agree |
| `""` | **-99** (None) | **0** | JIT silent wrong |
| `"99999999999999999999"` | **-99** (overflow ⇒ None) | **0** | JIT silent wrong |
| `"+7"` | 7 | 7 | agree — leading `+` accepted |

Interpreter semantics pinned by measurement, not assumption: **whitespace is
trimmed, a leading `+` is accepted, overflow yields `None` (not a saturated
value), and the empty string yields `None`.**

`parse_i64` / `parse_i32`, JIT — PROVED:

```
Runtime error: Function 'str.parse_i64' not found      <- stderr, twice
i64_42=27                                              <- garbage, and exit 0
```

Interpreter for the same source returns `42`, `-99` (for `"abc"`), `3`.

Native column — **measured, not inferred**. `compile --native` on a probe
without `??` (the `??` form fails closed with `[TryOperator]`, so the Option
behaviour itself is *unmeasurable* on native today — stated rather than
invented). Positive artifact check: `file` reports `ELF 64-bit LSB pie
executable`, the binary ran, rc=0.

```
N_42=42    N_abc=0    N_3ctl=3    N_dot=0
```

⇒ native strips the Option identically to the JIT, and follows the **strict**
runtime semantics (`"4.2"` → 0, not 4).

## 3b. Root cause of the "present 3 read as absent" mode

PROVED by reading `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1181-1201`
(`lower_coalesce`): `x ?? d` is lowered to a **`BinOp::NotEq` against
`HirExprKind::Nil`** — literally `if x != nil then x else d`.

When `x` is typed `TypeId::I64` — which is exactly what
`hir/lower/expr/mod.rs:1179` assigns to `parse_int` / `parse_i32` /
`parse_i64` — that comparison degenerates to an **integer compare against the
nil sentinel, and the nil sentinel is 3**. So `"3".parse_int() ?? -99` compares
`3 != 3`, takes the default, and reports a successfully parsed 3 as absent.

This closes the chain: the raw-`i64` typing is not merely *lossy*, it actively
manufactures a wrong answer for one specific legitimate input.

Note the in-file comment at `hir/lower/expr/mod.rs:1161-1179`: the
`parse_int | parse_i32 | parse_i64 => TypeId::I64` entry was **added
deliberately** by an earlier lane to fix a print-decode bug (a raw `i64` handed
to `rt_println_value` was decoded by bit pattern, so `"42"` printed as an f64
denormal). That fix was correct for its symptom but cemented the raw shape.
Stage 2 must not simply revert it — the print-decode path has to keep working,
which is another reason the tagged-nullable ABI of stage 1 is the right vehicle.

Second, distinct gap — the float family: `rt_string_to_float` already returns
`RuntimeValue::NIL` on failure, yet `"abc".parse_float() ?? -99.0` still yields
**0** on the JIT, i.e. the `!= nil` test does not fire on that NIL either. So the
tagged-nullable ABI alone is **not sufficient** in the Rust seed; the nil
representation used by `lower_coalesce` and the one returned by the runtime do
not agree. Stage 3 must fix that agreement, not just the HIR type. INFERRED
mechanism, PROVED symptom.

## 3c. Reproduced on a freshly built, unmodified baseline

To rule out a stale deployed binary as the explanation, the whole workspace was
rebuilt from the measured base sha in an isolated tree
(`cargo build --release -p simple-driver`, rc=0, fresh target dir, 57,259,744
bytes, enum-probe = 0 ⇒ Rust seed).

The freshly built binary reproduces the §3 table **byte for byte** on both
engines, including the `"3"` → `-99` inversion. The defect is in the source at
the base sha, not in a stale artifact. A working build + repro platform for
stage 1 therefore exists and is cheap to reconstruct.

## 4. Caller census — the premise inverts

Counted over `src/`, `test/`, `scripts/`, `*.spl` + `*.shs`, excluding `build/`
and `.claude/`.

| method | call sites | `??` | `unwrap_or` | `match` | `?` |
|---|---|---|---|---|---|
| `parse_int` | 420 | 281 | 11 | 25 | 4 |
| `parse_i64` | 51 | 23 | — | — | — |
| `parse_i32` | 72 | 6 | — | — | — |
| `parse_float` | 17 | 2 | — | — | — |
| `parse_f64` | 46 | 3 | — | — | — |
| `parse_f64_safe` | 0 | — | — | — | — |

**The tree already treats `parse_*` as Option-returning.** For `parse_int`, 321
of 420 sites are syntactically Option-consuming (`??`, `.unwrap_or`, `match`,
`?`); 9 more are comments. The residual bare-`val` sites bind the result and
inspect it later.

This overturns the framing that a fix "would break every caller currently
relying on the raw i64". **Essentially no caller relies on the raw i64.** The
JIT/native lowering is the outlier — it disagrees with the interpreter *and*
with the call sites.

What callers do on a parse failure today:

- On the interpreter: the `??` / `unwrap_or` default is taken. Correct.
- On JIT/native: `??` never fires (the value is a raw scalar, not an Option), so
  the failure default is **silently skipped** and 0 flows on — e.g.
  `args[0].parse_int() ?? 100` yields **0**, not 100, for a malformed argument.
- And for a legitimate input of `"3"`, `??` fires when it should not, so
  `parse_int() ?? 100` yields **100** for the input `"3"`.

## 5. Migration design

The in-tree precedent already exists and should be copied rather than invented.
The **pure-Simple** compiler already solves exactly this problem for `parse_f64`
in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2012-2050`: it
emits `rt_string_to_float`, marks the destination a runtime value, and records
the local's HIR type as `Optional(Float(64))` — with the in-file rationale
*"parse_f64 must keep the existing nullable tagged rt_string_to_float ABI so zero
remains distinct from parse failure."*

That is the correct shape, and it is what protects against the nil-sentinel
hazard: the result is a **tagged** runtime value, and a tagged int is `v << 3`,
so a successful parse of 3 becomes 24 and can never collide with the nil
sentinel 3. Boxing the *bare scalar coercion* instead would break every `??` /
`.?` / `.unwrap()` / arithmetic consumer of a `T?` in the tree; that route is
explicitly rejected.

### Stage 0 — measurement (this document). LANDED.

### Stage 1 — new Option-preserving int entry point
- Add `rt_string_to_int_opt(RuntimeValue) -> RuntimeValue` to **both** runtimes,
  with the `rt_string_to_float` tagged-nullable ABI: a tagged int on success,
  `NIL` on failure. Not a raw `i64`. Both runtimes must agree on **strict**
  whole-string semantics (matching the interpreter), and the existing
  `rt_string_to_int` strict/lenient divergence recorded in §2b must be resolved
  or documented at the same time.
- Link-level evidence required: `ld.lld`, `nm` at a real address (`nm -u` is
  blind to weak zero-size definitions), a `file`-confirmed executable, and
  running it.
- Verify the emitter passes real operands before implementing the receiver —
  implementing for an emitter that discards its operands converts a loud link
  error into a silent wrong answer.

### Stage 2 — route the int family, all six tables at once
- `parse_int | parse_i32 | parse_i64` → `rt_string_to_int_opt` in all six alias
  tables listed in §2; add `parse_i32` / `parse_i64` to `mangle.rs`.
- `hir/lower/expr/mod.rs:1179` → optional-int, not `TypeId::I64`.
- `to_int` / `to_i64` stay on `rt_string_to_int`, unchanged.
- Non-vacuity: sabotage `rt_string_to_int_opt` itself (not a shim) and confirm
  RED before GREEN.

### Stage 3 — float family
`rt_string_to_float` already returns `NIL` on failure, so the runtime half is
done; only the HIR type (`TypeId::ANY` at `:1385`) and the `??` recognition need
fixing. Cheaper than stage 2 and should follow it.

### Stage 4 — pure-Simple compiler parity
Apply the same treatment in `src/compiler/50.mir/`. Blocked on the known
stage-3 self-host blocker; must not be claimed until a self-hosted binary can be
built and re-verified.

### Stage 5 — `[TryOperator]` on native
`??` fails closed on `compile --native`, which is why the native Option column is
unmeasurable today. Until this is lifted, no native Option claim can be made.

## 6. Explicit non-goals

- **Do not** fix this by teaching callers to tolerate a sentinel. The point is to
  stop losing the Option.
- **Do not** add `parse_i64` / `parse_i32` to the existing alias tables pointing
  at `rt_string_to_int`. That would convert today's loud-ish
  `Function 'str.parse_i64' not found` into a silent wrong answer, which is
  strictly worse. Two prior lanes declined for exactly this reason and were
  right to.
