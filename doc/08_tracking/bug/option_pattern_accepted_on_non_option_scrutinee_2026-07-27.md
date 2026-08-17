# Bug: `Some(_)` patterns and `.unwrap_or` silently accepted on NON-Option values

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent wrong answers; type error degraded into bad data; engines disagree)
- **Found by:** lane OPTNIL, reproduced independently by the coordinator
- **Reconstructed:** the lane's original doc was clobbered off disk by a parallel
  session before landing; this is rewritten from the lane report plus the
  coordinator's own reproduction.

## Not what it first looked like

This was reported as "Option payloads bind as nil". That framing is **wrong** —
real `Option<T>` is correct on both engines for payloads `0, 1, 3, -7,
123456789`, across `match` / `if val` / `unwrap_or`, for
`Option<i64>`, `Option<text>` and `Option<struct>`. The prior-art
"JIT `Option<i64>` payload 3 reads as None" collision did **not** reproduce.

## The actual defect

`text.index_of` returns a **plain `i64`**, not `Option<i64>` — proven by
`idx + 1 == 7` with no unwrap. The compiler nonetheless **accepts `Some(_)`
patterns and `.unwrap_or` on non-Option receivers instead of erroring**.

A bare `val n = 6` reproduces every symptom with no `index_of` involved, so the
hole is in **type checking**, not in the producer. One raw value yields three
different wrong answers, because each consumer misdecodes the untagged scalar its
own way — and the two engines disagree:

| expression (`n` is a bare `i64` = 6) | JIT | interpreter |
|---|---|---|
| `match n: Some(i)` | takes the `Some` arm, binds **nil** | matches **neither arm — not even the `_` wildcard** |
| `n.unwrap_or(-99)` | **`<value:0x6>`** (tag box leaked into text) | `6` (returns the receiver) |
| `if val Some(k) = n` | branch **taken**, binds **nil** | not taken |
| bare `i64` passed through an `Option<i64>` **parameter** | binds **3** — a plausible wrong integer (`6>>1`) | falls through |
| `None.to_text()` | `nil` | **errors** |

The interpreter failing to match `_` is itself a second defect: a wildcard arm
must be unconditional.

## Where

- ~~`src/compiler/10.frontend/core/interpreter/eval_methods.spl:107` — Option
  handling is gated on `kind == VAL_STRUCT`, so a raw `i64` misses every branch
  and `unwrap_or` (:117) falls through returning the receiver.~~
  **NOW-WRONG (2026-08-01) — this described DEAD CODE.** `eval_methods.spl` was
  a duplicate shadowed by the package-local `_EvalOps` copies and was deleted in
  `f97dfbbb8ee`. Re-derived against the live `eval_method_call`
  (`_EvalOps/call_method_eval.spl:567-654`): it has **no Option/Result built-in
  method block at all**. There is no `unwrap` / `unwrap_or` / `is_some` /
  `is_none` / `unwrap_err` / `is_ok` / `is_err` arm anywhere in the live
  interpreter (`grep '"unwrap"' src/compiler/10.frontend/core/interpreter/`
  returns nothing). Its only `kind == VAL_STRUCT` branches are the `__dict`
  table and a user-method `func_table_lookup`, after which it hits
  `eval_set_error("no method '<name>' on struct")`. So the mechanism recorded
  here — "gated on `VAL_STRUCT`, raw `i64` misses every branch, `unwrap_or`
  returns the receiver" — is **not** the live pure-Simple behaviour. The live
  behaviour for a *struct* Option is a hard error, and for a raw `i64` receiver
  it is `no method 'unwrap_or' on int`. **The user-visible symptom this bug
  reports (`<value:0x6>` leaking from `unwrap_or`) therefore comes from the MIR
  lowering below, not from the interpreter** — which strengthens, not weakens,
  the `rt_unwrap_or_self` root cause. Whether the deleted block ever ran is
  UNKNOWN: the sabotage proof covered `eval_text_method`, whose sole call site
  is inside `_EvalOps`; `eval_method_call`'s external caller is
  `eval.spl:301`, so resolution there was never measured. **What would settle
  it:** nothing anymore — only one definition survives. **What is actionable:**
  if any Simple source calls `.unwrap()`/`.is_some()` on an Option struct under
  the pure-Simple interpreter, it errors today. That gap should be filed and
  fixed on `_EvalOps/call_method_eval.spl`, not rediscovered from the deleted
  file.
  **DONE (2026-08-01, second pass) — and it STRENGTHENS the `rt_unwrap_or_self`
  root cause below.** The gap was confirmed by *running* the pure-Simple
  interpreter (`core_interpret_expr` driven with the Rust seed as HOST ONLY over
  working-copy source, with a deliberately-failing SENTINEL row), then closed:
  `eval_option_result_method` in `_EvalOps/call_method_eval.spl` now implements
  `unwrap`, `unwrap_or`, `unwrap_err`, `is_some`, `is_none`, `is_ok`, `is_err`.
  Two consequences for THIS bug:
  1. **The interpreter is now eliminated as a suspect by construction.** Its
     `unwrap_or` returns the payload for `Some`/`Ok` and evaluates the default
     argument otherwise; it **never** returns the receiver. There is no
     `_or_self` fallback anywhere on the interpreter path. So any surviving
     `<value:0x6>` leak from `unwrap_or` is the MIR lowering — the diagnosis
     below is confirmed, not merely inferred from the interpreter's silence.
  2. The `VAL_STRUCT` gating story is superseded but its *shape* was
     half-right, and the reason matters. Measured encoding: there is **no
     `VAL_ENUM`** in this interpreter; an Option is either BOXED (a
     `VAL_STRUCT` with `__tag` at field 0) or FLAT (the raw word, `nil` =
     `None`). A raw `i64` receiver really does miss any `VAL_STRUCT`-gated
     branch — which is exactly why the new arm is gated **before** the per-kind
     dispatch and discriminates on `__tag`, never on `kind` or on the struct
     name. (The struct name is unusable: `eval_enum_variant_call` produces
     `"Option::Some"` while `parse_int` produces plain `"Option"`.)
  Regression pin:
  `test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl`.
  Nothing here retracts the `rt_unwrap_or_self` item; fix #2 in the plan below
  still stands.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:388-396` —
  `option_payload_or_self` emits **`rt_unwrap_or_self`** ("return the receiver if
  it is not an Option"), typed `i64` while the value stays tag-boxed, producing
  `<value:0x6>`. Also :560, :598 and `cranelift_codegen_adapter.spl:1276`.

**That `_or_self` fallback is the design decision that converts a type error into
a silent wrong answer.**

## Blast radius

In owned `src/**`: 11,410 `Some(`, 911 `if val Some(`, 1,168 `.index_of(`.
**17 sites confirmed dangerous** — a bare-`i64` `index_of` result fed into an
Option form — including **4 in `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl`**.
Those 4 are the direct cause of the LLM lane's "every MCP tool argument silently
arrived empty" (`_extract_arg` returned `""` for every key). Causal chain closed.

## Reproduce

```
bin/simple run build/optnil_verify.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/optnil_verify.spl
```

## Interim mitigation

At the 17 sites, test `index_of`'s real `-> i64` contract directly:
`if i >= 0:` — do not destructure it as an Option.

## Why no fix landed

Tightening this changes compile behaviour at 11,410 `Some(` sites and needs a
staged warn→error migration; and the primary hole is in a compiler tree where
other lanes were live. A regression spec was also deliberately not added: it
would fail against `main` until the fix lands.

## Next step

1. Decide the contract: either `index_of` returns `Option<i64>` (and callers
   migrate) or it stays `i64` and Option forms on non-Option scrutinees become a
   **compile error**. The current middle ground is the bug.
2. Delete or gate `rt_unwrap_or_self` so a non-Option receiver is rejected rather
   than silently passed through.
3. Fix the interpreter's wildcard arm so `_` always matches.
4. Repair the 17 confirmed sites, starting with `jsonrpc.spl`.

## Sites repaired

### Contract, re-measured (lane IDXFIX2, `build/idxfix2/*.spl`)

`bin/simple run` and `SIMPLE_NO_JIT=1 bin/simple run` gave **identical** results
for every probe, so on the current toolchain this defect is not engine-specific.

| expression (`s = "hello"`; found = 1, miss = -1) | result |
|---|---|
| `match idx: Some(i) / nil` | **always** `Some`, binds **nil** |
| `idx == nil` | **always false** — the not-found branch is dead code |
| `idx != nil` | **always true** — the guard never rejects `-1` |
| `idx ?? N` | returns raw `idx`; `-1` leaks through |
| `idx.?` | **truthiness** — false at index `0`, true at `-1` (inverted at both ends) |
| `idx.unwrap()` | `nil` when found; `<value:0xff..ff>` when not |
| `s.find(x).unwrap_or(-1)` | `<value:0x6>` / `<value:0xff..ff>` |
| `"a/b/c".last_index_of("/")` = 3, matched as Option | takes the **nil** arm |
| `"abc".last_index_of("/")` = -1, matched as Option | takes the **Some** arm, binds nil |

**`text.last_index_of` / `rfind` are also plain `i64`.** `src/lib/text.spl:61`
declares `-> i64?`, but the builtin intercepts first
(`_EvalOps/access_literal_assign_eval.spl:259-268` returns
`val_make_int(s.last_index_of(needle))`; `compiler/cg_expr.spl:555` emits
`spl_str_last_index_of`), so callers see a raw `i64`. Any earlier note calling
`last_index_of` "correctly Option-shaped" is wrong.

> **Citation corrected 2026-08-01 — conclusion holds, history did not.** This
> cited `eval_methods.spl:459`, which was dead code. Two corrections: (1) the
> live arm lives in `_EvalOps/access_literal_assign_eval.spl`; (2) between
> 2026-07-27 and 2026-08-01 the live text-method table had **no**
> `last_index_of`/`rfind` arm at all — so "the builtin intercepts first" was
> false for the interpreter lane during that window; `last_index_of` fell
> through to `eval_set_error` and returned `-1`/`VAL_NONE`. It became true
> when `f97dfbbb8ee` added the arm. The **raw-`i64`, `-1`-for-miss contract is
> confirmed** on the live code, and the `?? -1` the old citation quoted was
> deliberately dropped (it was dead on a miss and corrupted a genuine hit at
> index 3, the nil sentinel). See
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

### Repaired (lane IDXFIX2 — 28 files)

Rule applied: `>= 0` = found, `< 0` = not found; each site's existing not-found
branch was kept verbatim, only the test changed.

| file | shape |
|---|---|
| `src/app/mcp/api_tools.spl`, `src/lib/nogc_async_mut/mcp/api_tools.spl` | `.? == false` guard + `(idx ?? 0)` (4 each) |
| `src/lib/nogc_async_mut/mcp/resources.spl` | `q_idx.?` + `(q_idx ?? 0)` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/resource_tracker.spl` | `.? == nil` + `?? 0` / `?? (len-1)` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/process_monitor.spl` | `.? == nil` + `?? 0` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http/accept_encoding.spl` | `.? and …` (3 each) |
| `src/lib/nogc_async_mut/http_server/parser.spl` | `.? and …` (5) |
| `src/lib/nogc_sync_mut/http_server/mime.spl` | `dot_idx == nil` |
| `src/lib/nogc_sync_mut/ui_test/{parse,client,http}.spl` | `== nil` / `!= nil` (8) |
| `src/lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/graph.spl` | `index_of(x) ?? 0` |
| `src/{app,lib/nogc_sync_mut,lib/nogc_async_mut}/debug/remote/protocol/trace32.spl` | `colon_idx != nil` |
| `src/app/llm_caret/claude_full/constants/files.spl` | `dot == nil` |
| `src/app/interpreter/utils/path_resolution.spl` | `idx.?` + `idx.unwrap()` |
| `src/app/mcpgdb/debug_backend_common.spl` | `last_index_of` + `match Some(idx)` |
| `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` | `last_index_of` + `match Some(i)` |
| `src/os/services/launcher/launcher_registry.spl` | `last_index_of` + `case Some(idx)` (2) |
| `src/os/apps/shell/_ShellTools/text_tools.spl` | `== nil` + `.unwrap()` |

### Live failures the repairs removed (A/B, `build/idxfix2/verify*.spl`)

| function | before | after |
|---|---|---|
| `api_tools.extract_nested_string` on valid JSON | `""` — **never extracted anything** | `v1` |
| `http_server/parser` blank line = end of headers | `need-more` — **terminator unreachable**, headers never finished | `END-OF-HEADERS` |
| `ui_test/client` contains-assertion on a miss | `true` — **the assertion could never fail** | `false` |
| `ui_test/http.extract_body` with no `\r\n\r\n` | `"defgh"` — body sliced from offset 3 of an unrelated response | `""` |
| `mime_from_path("noext")` | treated the whole path as the extension | `application/octet-stream` |
| `accept_encoding` q-value `".5"` | `nodot` → q parsed as 0 | `int=[] frac=[5]` |

### Deferred (outside this lane's owned paths)

| file | owner |
|---|---|
| `src/os/tools/net/wget_tool.spl:31,41,54,68` (`if val Some(i) = …`) | URL-parsing lane |
| `src/lib/{nogc_sync_mut,nogc_async_mut}/ftp_utils.spl:501,508` (`at_idx.?` with no `>= 0`) | URL-parsing lane |
| `src/lib/nogc_async_mut/http_server/proxy.spl:310` (`qmark.? and qmark >= 0`) | URL-parsing lane |
| `src/os/services/llm/_McpOsServer/helpers.spl:56,63,72,80,83` | lane UIQUERY |
| `src/lib/common/ui/parse/{sdn,sdn_tree}.spl` (`index_of(n) ?? -1`) | lane UIQUERY — benign no-op |

### Separate defects found while repairing

1. **`text[a..b]` (double-dot range slice) is corrupt.** `"/a/b"[0..2]` yields a
   text whose `.len()` is `-1` and which makes string interpolation swallow the
   entire output line; `[0:2]` and `.slice(0,2)` are correct. Pre-existing —
   it had silently broken `parent_dirname` in
   `src/app/interpreter/utils/path_resolution.spl`, now switched to `[0:idx]`.
2. **`[T].index_of(v)` returns `-1` even when the element is present**
   (`build/idxfix/arr2.spl`). Array `index_of` looks unimplemented; distinct
   from the Option-shape bug and not fixed here.
3. `.?` on an `i64` is plain truthiness, so it is wrong at *both* ends: it
   rejects a genuine match at index `0` and accepts the `-1` sentinel. Sites
   half-repaired as `if x.? and x >= 0:` still drop index-0 matches.

## 2026-08-01: array accessors are a REACHABLE TRIGGER SURFACE for this hole

Independently reproduced on the seed binary built 2026-08-01 14:48. This section
adds *which real API invites the mistake*, which the doc previously did not say.

`[T]` accessors split into two different return shapes, and only one is `T?`:

| accessor | declared return type | source |
|---|---|---|
| `at(i)` | **`T?`** (`HirType::Pointer{inner: elem}`) | `hir/lower/expr/mod.rs:1257` |
| `first` / `last` / `get` / `max` / `min` | **`T`** (bare element) | `hir/lower/expr/mod.rs:1271` |

Because `.at()` legitimately returns `T?`, `match xs.at(0): case Some(v)` is
correct and now works. Writing the visually identical `match xs.first(): case
Some(v)` is silently wrong — `first` is `T`. This is an easy and natural mistake,
and neither engine reports it.

Measured on `xs = [10, 20, 30, 40, 50]`, one program, one binary:

| expression | correct | JIT | interpreter |
|---|---|---|---|
| `match xs.at(1)` | `Some(20)` | `Some(20)` — correct | `Some(20)` — correct |
| `match xs.first()` | *type error* | `Some(5e-323)` — **denormal float garbage** | **no arm taken, no output** |
| `match xs.last()` | *type error* | `Some(<denormal>)` | no arm taken |
| `match xs.get(1)` | *type error* | `Some(<value:0x14>)` — undecoded tag box (0x14 = 20) | no arm taken |
| `match xs.get(99)` | *type error* | `None` | `None` |

Both engines exit **0** with no diagnostic.

**New manifestation:** the table above documents JIT binding **nil** for a
non-Option scrutinee. Via `first`/`last` it instead binds a **denormal float** —
the element's `i64` bit pattern reinterpreted as `f64` (`10` -> `5e-323`). So the
JIT symptom is not always nil; it is "whatever the consumer's own misdecode
yields", which is harder to spot because it still prints inside `Some(...)`.

Minimal repro with **no array and no `.at()` at all** (`typehole.spl`):

```simple
fn plain() -> i64:
    return 42

fn main():
    print("start")
    match plain():
        case Some(v): print("Some({v})")
        case None: print("None")
    print("end")
```

JIT prints `start` / `Some(<denormal>)` / `end`; the interpreter prints `start` /
`end`, taking neither arm. This confirms the root cause is the type checker
accepting Option patterns on a non-Option scrutinee, not anything array-specific
-- the array accessors merely make it easy to reach.

**Not a defect in `first`/`last`/`get`:** returning `T` is their defined
contract. The defect is only that the Option pattern is accepted against them.

## 2026-08-01 (lane OPTPAT): the hole is NOT array-shaped, and the JIT is not where anyone has been looking

Base sha `9349ff90f60`. Driver built from that sha — the deployed `bin/simple`
was built 14:48, **37 minutes before** the base commit (15:25), so it was used
only for the baseline and never for verifying a change. Probes:
`build/optpat/probe1.spl`, `probe2.spl`.

### 1. Blast radius is EVERY type, not just the accessors (PROVED)

The section above establishes array accessors as *a* trigger surface. They are
not the boundary. Under the default engine an `Option` pattern is taken against
a scrutinee of **any** type, and each type produces its own wrong binding:

| scrutinee | default engine (JIT) | `SIMPLE_EXECUTION_MODE=interpreter` |
|---|---|---|
| `val n: i64 = 6` | `Some` taken, binds **`<value:0x6>`** | takes `_` |
| `val t = "abc"` | `Some` taken, binds **the whole text** `abc` | takes `_` |
| `val b = true` | `Some` taken, binds **`nil`** | takes `_` |
| `val xs = [1,2]` | `Some` taken, binds **the whole array** | takes `_` |
| `if val Some(k) = n` (`n=6`) | branch taken, `k=<value:0x6>` | not taken |

So no grep over container accessors — or over any API surface — bounds this
defect. Only a type check does. Text accessors behave identically
(`s.index_of("l")` binds `0.0` under a pattern but returns `2` directly;
`s.last_index_of("/")` binds `<value:0x5>` but returns `5` directly).

### 2. Correction: the interpreter DOES take an explicit `_` arm

This doc's opening table says the interpreter "matches neither arm — not even
the `_` wildcard", and the section above reports "no arm taken, no output".
Re-measured with an explicit `case _` present, the interpreter **takes it**
every time (all 5 rows above). The earlier probes used `case None` as the
fallback, which correctly does not match. The "wildcard is not unconditional"
second defect therefore **does not reproduce** at this sha; next-step item 3
below should be treated as closed unless re-demonstrated.

### 3. Two different corruption shapes inside the same family (PROVED)

On `xs = [10, 20, 30]`, matched as `case Some(v)` under the default engine:

| accessor | bound value | direct call |
|---|---|---|
| `.first()` | **denormal float** (element i64 bits read as f64) | `10` correct |
| `.min()` | **denormal float** | `10` correct |
| `.last()` | **`<value:0x1e>`** tag box | `30` correct |
| `.get(1)` | **`<value:0x14>`** tag box | `20` correct |
| `.max()` | **`<value:0x1e>`** tag box | `30` correct |
| `.at(0)` | **`10` — CORRECT** | — |

The section above records `last` as denormal; at this sha it is a tag box. The
manifestation is not stable per-accessor, which is another reason not to
fingerprint this bug by its symptom. All five return the **correct** value when
called directly — only the pattern corrupts.

### 4. Value-3 control (the nil sentinel IS 3)

- `val three: i64 = 3` → falls to `_` on **both** engines: `rt_is_some` means
  only "not the nil sentinel", so a genuine 3 reads as absent.
- `[3,7].first()` as `Some(v)` → falls to `_` (same collision).
- `[3,7].at(0)` → **`Some(3)`, correct** — a real Option that silent-nil cannot
  produce. This is the control that separates "`at` is genuinely `T?`" from
  "everything else is not".

### 5. Retyping the five to `T?` (option (b)) is rejected ON EVIDENCE

Not on the strength of the in-tree comment — that comment
(`hir/lower/expr/mod.rs:1281`, "Returns element type (or Option<element>)") is
an unresolved hedge, not a stated decision, so it was verified rather than
trusted. The **runtime ABI** settles it: `rt_array_first` / `rt_array_last` /
`rt_array_get` are declared `int64_t rt_array_*(SplArray*, ...)`
(`src/runtime/runtime.h:378-380`) and return the raw element word
(`runtime_native.c:4600-4617`). `rt_array_at` is a **separate** Option producer
that `runtime_native.c:5245-5265` documents as *deliberately* not built on
`rt_array_get`, precisely because `rt_array_get` reports a miss as the raw nil
sentinel 3. Bare `T` is correct for the five; retyping them would need a runtime
ABI change plus every direct call site, and would still not touch the `text`,
`bool` or array scrutinees in §1.

### 6. The cited static locus is NOT on the path that produces the symptom (PROVED)

- `hir/lower/expr/control.rs:566-603` (`lower_pattern_condition`,
  `Pattern::Enum`) routes `Some`/`None` to `rt_is_some`/`rt_is_none` whenever
  `!subject_enum_owns_variant` — i.e. for any non-enum scrutinee. This is a real
  static hole, but an **unconditional debug print inserted into that arm emitted
  zero output** for a probe that triggers the defect 8 times.
- `simple compile` and `simple compile --backend=llvm` never reach it either:
  both **fail closed** first with
  `cannot compile to standalone SMF: main: [PatternMatch]`. The **native half of
  this defect is unmeasurable, not merely unmeasured.**
- `interpreter_patterns.rs` (`Pattern::Enum` arm) is the live decision point for
  the interpreter: a non-`Value::Enum` value falls through to `Ok(false)`, which
  is the `_`-arm behaviour in §2.

### 7. There is a THIRD match implementation, and it is the default engine

A default-off diagnostic added to `interpreter_patterns.rs` fires **8/8** on the
interpreter for `probe1.spl` and **0/8** on the default engine for the identical
program. So the JIT — the default for a bare `simple foo.spl`, and the half that
binds garbage rather than falling through — uses neither `hir/lower` nor
`interpreter_patterns`. **Locating that third implementation is the next step**;
until it is found, no instrument and no fix covers the engine that actually
produces the wrong values.

### 8. Instrument landed — warn-only, DEFAULT OFF

`SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` makes `interpreter_patterns.rs` report an
`Option`/`Result` pattern tested against a non-enum, non-nil, non-object value.
It discriminates on the **runtime value**, not an inferred type, so it has no
false positives by construction: on `probe1.spl` it flagged exactly the 8 bad
sites and neither of the 2 correct `.at()` sites.

**Dynamic fallout, measured before landing:** a 1-in-180 sample of the spec
tree (**104** specs, every 180th of 18,704; 68 rc=0, 28 rc=1, 8 timed out at
12s) run under the interpreter with the gate ON emitted **0** warnings. So
turning the gate on costs nothing on the sampled workload. This bounds the
*runtime* fallout on the interpreter path only; it does **not** bound the static
fallout of a compile-time reject, which is why no promotion is proposed here.

Deliberately **not** promoted to an error. Measured fallout surface in owned
`src/**` (excluding `build/` and `.claude/`): **2,746** Option-shaped pattern
sites (`case Some(` 1,740 + `if val Some(` 997 + `while val Some(` 9) and
**4,211** Result-shaped sites, across **620** files. Promoting now would be
staged on the wrong half anyway, since the instrument cannot see the JIT (§7).

### Next step (superseded by the 2026-08-01 lane below)

1. ~~**Find the third match implementation**~~ — **DONE**, see §9.
2. Then re-measure fallout with both engines instrumented, and only then decide
   warn→error promotion.
3. Item 3 of the old list ("fix the interpreter's wildcard arm") appears closed —
   see §2.

## 2026-08-01 lane OPTPAT-JIT (base `f7b68068a3e854023f06d92beb3071854d85973c`)

### 9. The third implementation is `hir/lower/stmt_lowering.rs` (PROVED by instrumentation)

Not by reading — by four simultaneous **unconditional** `eprintln!` probes, one
per candidate match implementation, in a single build, run against an 11-site
probe (`match xs.first()/last()/get(1)/max()/min()`, bare `i64`/`text`/`bool`
scrutinees, plus two correct `.at()` controls and the value-3 control):

| probe site | default engine (JIT) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt` (`Pattern::Enum`) | **11** | 0 |
| `interpreter_patterns.rs` `Pattern::Enum` | 0 | **11** |
| `hir/lower/expr/control.rs` `lower_pattern_condition` (`Pattern::Enum`) | 0 | 0 |
| `codegen/instr/pattern.rs` `compile_pattern_test` (`MirPattern::Variant`) | 0 | 0 |

`[jit-fallback]` count on the JIT run: **0**, so the JIT was genuinely the engine
under test.

The prior lane's elimination of `hir/lower/expr/control.rs` was **correct but
mislabelled**: that file is the *expression*-form twin, and the probe used
statement-position `match`. The JIT path is
`parse -> hir::lower -> lower_to_mir -> JitCompiler` (`driver/src/exec_core.rs`
`run_source_in_memory_native`), so HIR lowering *is* on the JIT path — just the
statement half of it. `codegen/instr/pattern.rs` never fires because the match is
already lowered to `HirStmt::If` + `rt_is_some` before MIR sees it; MIR pattern
codegen (and its LLVM/bytecode `MirPattern` consumers) is dead for this shape.

### 10. There is a FOURTH — and `while val` checks nothing at all (PROVED)

Attributing each surface form separately, with all four probes live:

| form | probe that fired | JIT result on a value that is not an Option |
|---|---|---|
| `match subj: case Some(v)` (statement) | `stmt_lowering.rs` | arm taken, binds garbage |
| `if val Some(k) = subj` | `stmt_lowering.rs` | branch taken, `k = <value:0x6>` |
| `val r = match subj: case Some(v)` | `expr/control.rs` | arm taken, `r = <value:0x6>` |
| `while val Some(w) = xs.first()` | **none of the four** | loop entered, `w = 0` |

`while val` reaches **no** pattern-condition lowering at all: `Node::While` in
`hir/lower/stmt_lowering.rs` lowers only `while_stmt.condition` through
`lower_condition` and never emits a pattern test or a payload extraction, so the
let-pattern is silently dropped. That is a **separate, unfixed defect** — filed
here rather than fixed in this lane — and it means the 9 `while val Some(` sites
counted in §8 are not merely mis-typed, they are unchecked.

### 11. Nullability is NOT erased by HIR — a sound static check is possible (PROVED)

The resolved `HirType` of the scrutinee at the decision point, printed from the
`stmt_lowering.rs` probe:

| probe site | resolved subject type | outcome |
|---|---|---|
| `.first()/.last()/.get(1)/.max()/.min()`, bare `i64` | `Int { bits: 64 }` | corrupt |
| bare `text` | `String` | corrupt |
| bare `bool` | `Bool` | corrupt |
| `.at(0)` (both controls) | `Pointer { inner: i64 }` | **correct** |
| `fn f() -> i64?` and `val x: i64? = 6` | `Pointer { inner: i64 }` | **correct** |

A nullable `T?` resolves to `HirType::Pointer`, a bare `T` to
`Int`/`Float`/`Bool`/`Char`/`String`. The separation is exact on the probe: all 9
statically-impossible sites are bare scalars/text, both legitimate Option sites
are `Pointer`. So the JIT half **can** be instrumented soundly on the static
type, which the runtime cannot do (`i64 6` and `i64? = 6` are bit-identical at
runtime — see §13).

### 12. Instrument landed on the JIT path — warn-only, DEFAULT OFF

`src/compiler_rust/compiler/src/hir/lower/option_pattern_shape_diag.rs`, called
from **both** HIR twins (`stmt_lowering.rs` statement form, `expr/control.rs`
expression form). Same switch as the interpreter check —
`SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` — so one run now instruments both engines.

Reports only when the resolved subject type is `Int`/`Float`/`Bool`/`Char`/
`String`. `Pointer`, `Enum`, `Struct`, `Any`, `Unknown`, arrays, tuples and dicts
are deliberately **not** reported: an under-report is correct here, a false
positive is not (nullable arrays/tuples were not measured, so they stay silent).

Verified at this sha with the shipped binary:

- gate OFF on the 11-site probe: **0** warnings; stdout byte-identical to the
  gate-ON run, so the diagnostic changes no behaviour.
- gate ON on the 11-site probe: **9** warnings — exactly the 9 bare-scalar/text
  sites; the 2 `.at()` sites are not flagged.
- gate ON on the nullable probe (`fn f() -> i64?`, `val x: i64? = 6`): **0**
  warnings, and all three rows answer correctly under the JIT.
- gate ON on the expression form: fires, tagged `expression form`.

**Nothing was promoted to an error.** The JIT still binds the corrupt value; this
lane makes that visible, it does not change it.

### 13. The interpreter's own check has a FALSE POSITIVE, and the interpreter is wrong for `val x: i64?` (PROVED)

§8 claimed the interpreter check has "no false positives by construction". That
is **not true for a nullable local**. Measured on the same binary:

| row | JIT | interpreter | interpreter, gate ON |
|---|---|---|---|
| `fn f() -> i64?` returning 6 | `Some 6` | `Some 6` | silent |
| `fn f() -> i64?` returning nil | `_` | `_` | silent |
| `val x: i64? = 6` | `Some 6` | **`_` — WRONG** | **warns** |

A locally-declared `i64?` stays a raw `Value::Int` in the interpreter, so
`case Some(v)` does not match it and the value-keyed check flags it. Two
consequences: the interpreter is the wrong engine for `val x: T?` locals, and no
*runtime*-keyed check can be sound for scalars, because `i64 6` and `i64? = 6`
are the same bits. The static check in §12 is sound precisely because HIR has not
yet erased the distinction.

### 14. Next step (supersedes §"Next step" above)

1. Re-measure fallout with **both** engines instrumented (this lane's sample is
   in §15) and only then decide warn→error promotion.
2. Fix `Node::While` to lower the let-pattern (§10). Until then `while val
   Some(x) = ...` is unchecked on the JIT.
3. Fix the interpreter's handling of `val x: T?` locals (§13), which currently
   answers `_` where the JIT answers `Some`.

### 15. Fallout of the JIT-path instrument, measured (not estimated)

Sample: every 300th `*_spec.spl` of 18,704 = **62** specs, run under the
**default (JIT)** engine with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` and a 15 s
timeout, at base `f7b68068a3e`.

| outcome | count |
|---|---|
| rc = 0 | 45 |
| rc != 0 | 13 |
| timed out at 15 s | 4 |
| **`option-pattern-shape` warnings** | **8, in 2 files** |

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_51to74_spec.spl` — 6
- `test/03_system/stdlib/dynload/dynload_macos_system_spec.spl` — 2

Neither spec file contains a `Some(` of its own: the warnings come from the
**imported library closure** those specs pull in, which is lowered in the same
run. So unlike the interpreter half (§8: 0 warnings on 104 specs), the JIT half
has live hits in ordinary library code, which is consistent with §7 — the
interpreter instrument was measuring the engine that does not have the bug.

**Known gap in the instrument:** the warning carries no source span, so a hit
names the *run*, not the offending line. Adding a span is the obvious next
improvement and is required before any warn→error promotion can be triaged.

## 2026-08-01 lane WHILELET (base `05231d6c69fe9b542fc595a046a87a8de539f3b1`)

### 16. §10 / §14.2 FIXED: `Node::While` now lowers its let-pattern

`hir/lower/stmt_lowering.rs` `Node::While` ignored `while_stmt.let_pattern`
entirely — it lowered only `while_stmt.condition`. A boxed Option is truthy, so
the loop was entered unconditionally (even when the first value was `None`), the
subject was never pattern-tested, and no payload extraction was emitted, so the
binding read `0`. That is the FOURTH match-lowering path, and it did not check
anything at all.

Fixed by desugaring the let-pattern form to the shape the pure-Simple parser
already produces for it (`parse_while_stmt`,
`src/compiler/10.frontend/core/parser_stmts.spl`):

```
loop:
    val $while_let_subject = EXPR
    if <pattern matches>:
        <payload bindings>
        BODY
    else:
        break
```

`HirStmt::Loop` + `If` + `Break` rather than `HirStmt::While`, because the
subject `Let` must run inside the loop before the test and a `While` condition is
one expression with no room for a preceding statement. The pattern test and the
payload extraction reuse the *same* `if_let_pattern_condition` /
`extract_pattern_bindings` / `build_pattern_binding_stmts` owners the `if val`
form uses, so the two forms cannot drift apart again. `HirStmt::Loop` has no
invariants slot; a `while val <pattern>` carrying `invariant:` clauses is now a
loud `LowerError::Unsupported` rather than a silent drop (no site in the tree
combines the two).

The non-pattern `while` path is byte-identical to before — the new code sits
entirely inside `if let Some(pattern) = &while_stmt.let_pattern`.

### 17. The binding family, measured (PROVED, both engines, `[jit-fallback]` = 0)

Each form in its own file, run through `simple run` on a debug build of the base
sha and of the fixed sha; the value-3 control `[3,7].at(0)` → `Some 3` is present
in every file and fired in every run, so the engine was genuinely executing.
Expected values are hand-computed, not cross-engine agreement.

| # | form | expected | base JIT | fixed JIT | base interp | fixed interp | verdict |
|---|---|---|---|---|---|---|---|
| A | `while val Some(w) = xs.at(i)` | `sum=21 it=3` | `sum=0 it=9` | **`sum=21 it=3`** | `21/3` | `21/3` | **dropped silently → FIXED** |
| B | `while val Some(w) = f()` where `f() -> i64?` | `sum=6 it=3` | `sum=0 it=9` | `sum=0 it=0` † | `6/3` | `6/3` | **dropped silently → FIXED; † see §18** |
| C | `while val w = f()` (plain-identifier form) | `sum=3 it=2` | `sum=0 it=9` | **`sum=3 it=2`** | rc=1 ‡ | rc=1 ‡ | **dropped silently → FIXED; ‡ see §19** |
| D | `while var Some(w) = f()` | `sum=3 it=2` | `sum=0 it=9` | **`sum=3 it=2`** | `3/2` | `3/2` | **dropped silently → FIXED** |
| K | `while val Some(w) = f()` where the FIRST value is `None` | `it=0` | `it=9` | **`it=0`** | `0` | `0` | **dropped silently → FIXED** (loop was entered on `None`) |
| T | `while val Some(dir) = <text? local>` | `n=4 last=""` | *no output at all*, rc=0 | **`n=4 last=""`** | `n=0` § | `n=0` § | **dropped silently → FIXED; § pre-existing interp `val x: T?` defect (§13)** |
| U | `while val Some((a,b)) = f()` (tuple payload) | `s=13 n=2` | `s=0 n=9` | `s=0 n=2` ¶ | `13/2` | `13/2` | **trip count FIXED; ¶ payload gap is pre-existing, see §20** |
| E | `if val Some(k) = ...` (statement) | `k=3` | `k=3` | `k=3` | `k=3` | `k=3` | binds correctly, unchanged |
| F | `elif val Some(k) = ...` | `k=7` | `k=7` | `k=7` | `k=7` | `k=7` | binds correctly, unchanged |
| G | `val g = match ...` (expression form) | `11` | `11` | `11` | `11` | `11` | binds correctly, unchanged |
| H | `match ...` (statement form) | `v=3` | `v=3` | `v=3` | `v=3` | `v=3` | binds correctly, unchanged |
| I | match-arm guard carrying a binding | `v=7` | `v=7` | `v=7` | `v=7` | `v=7` | binds correctly, unchanged |
| J | `for (a, b) in pairs` destructuring | `46` | `46` | `46` | `46` | `46` | binds correctly, unchanged |

There is no expression-form `while` in the AST (`Expr` has `If` and `Match` but
no `While`), so the statement form is the whole while-let surface.

Which lowering site each form reaches, re-attributed at this sha:

| form | site |
|---|---|
| `while val`/`while var` (before) | **none of the four** — pattern dropped |
| `while val`/`while var` (after) | `stmt_lowering.rs` `Node::While` → `if_let_pattern_condition` → `lower_pattern_condition_stmt` |
| `if val` / `elif val` (statement) | `stmt_lowering.rs` `lower_pattern_condition_stmt` |
| statement `match` | `stmt_lowering.rs` `lower_pattern_condition_stmt` |
| expression `if val` / `match` | `expr/control.rs` `lower_pattern_condition` |
| interpreter, all forms | `interpreter_patterns.rs` `Pattern::Enum` (while-let via `interpreter_control.rs:354`, which was already correct) |

### 18. † The value-3 miss is PRE-EXISTING and shared with `if val` and `match`

Form B stops immediately because its first value is the integer **3 — the nil
sentinel**. Isolated with two controls at the same base sha:

- `while val Some(w) = f()` over `4,3,2,1`: fixed JIT gives `sum=4 it=1` — it
  stops exactly at the 3.
- the same loop over `6,5,4` (no 3): both engines give `sum=15 it=3`.
- **decisive control, on code this lane did not touch:** `if val Some(w) =
  f_returning_3()` prints `none` and `match f_returning_3()` picks `case _` — on
  the **base** binary as well as the fixed one.

So `rt_is_some` on a raw `i64?` holding 3 answers false on the JIT for *every*
pattern form. Not introduced here, not fixed here.

### 19. ‡ `while val w = <i64?>` fails LOUDLY on the interpreter (pre-existing)

`error: semantic: type mismatch: cannot convert enum to int`, rc=1, at the base
sha and after the fix. A loud failure, not a silent wrong answer, and only on the
interpreter — the JIT answers correctly after the fix. Filed here, not fixed.

### 20. ¶ Nested tuple sub-pattern payloads bind 0 on the JIT (pre-existing)

`Some((a, b))` binds `a=0 b=0` under the JIT for **`if val` and `match` too**, at
the base sha and after the fix — so it is a `build_pattern_binding_stmts`
sub-pattern gap, not a while-let gap. The while-let trip count is now correct
(2, was 9); only the payload is still wrong. Consistent with the known
"enum payload sub-pattern, nesting depth" family.

### 21. Native column: unmeasurable

`match` on an enum has no native lowering — `compile --native` fails closed with
`[PatternMatch]` — so no native value can be reported for any row above. Stated
rather than invented.

## 2026-08-02 lane OPTPAT-RESID (base `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`)

Four residual defects, all measured on a debug driver built from that sha and
from the modified tree, with `simple run` (NOT `simple test`, which forces the
interpreter and ignores `SIMPLE_EXECUTION_MODE`). `[jit-fallback]` = 0 on every
JIT run below. The interpreter is the true-positive control and answers every
row correctly at both shas.

### 22. §"scope limit of `5ce2f653a49`" FIXED: struct sub-pattern inside an array/tuple element

`bind_subpattern` (hir/lower/stmt_lowering.rs) had arms for `Identifier`,
`Typed`, nested `Enum`, `Tuple` and `Array`, and a `_ => {}` that swallowed the
two STRUCT spellings. The refutability half already handled them —
`subpattern_condition` routes both `Pattern::Enum{name:"_"}` and
`Pattern::Struct` to `struct_fields_condition` — so the arm was SELECTED
correctly and then every binder inside it read the zeroed stack.

Measured at base, JIT (interpreter correct on all four):

| form | base JIT | expected |
|---|---|---|
| `case Items([Point(a, b)])` (struct in an ARRAY element) | `0` | `47` |
| `case Pair((Point(a, b), k))` (struct in a TUPLE element) | `2` | `472` |
| `case [Point(a, b)]` (struct in a TOP-LEVEL array pattern) | `0` | `47` |
| `case Point(a, b)` (top-level struct — control) | `47` | `47` |

The `2` in row two is the diagnostic detail: the sibling `k` bound correctly and
only the struct fields were zero, so this is a binder gap, not a slot-addressing
gap.

Fixed by `bind_struct_fields`, the binder twin of `struct_fields_condition` and
deliberately identical in addressing (`FieldAccess { field_index }` over a
receiver retyped to the struct). It patches `ctx.locals[i].ty` to the concrete
field type for the same reason the `class_struct_fields` path does — MIR reads
`local.ty`, not `HirStmt::Let.ty`.

**The double-emit the earlier scope note warned about cannot happen, for two
independent reasons.** (1) Reachability: `build_pattern_binding_stmts` claims
both of its own struct positions BEFORE any `bind_subpattern` call — a
top-level struct returns out of the `Pattern::Enum` block, and a struct sitting
directly in an enum payload slot is taken by the `else if let Pattern::Enum {
payload: Some(..) }` arm, whose `else` is the only branch that calls
`bind_subpattern`. So a struct reaches the new arm only from a sequence element
or a deeper nested-payload walk, which neither of those paths visits. (2) A
structural guard rather than an argument: `already_bound` skips a local that
already has a `Let` in the output, so the same binding can be emitted at most
once per arm whatever the caller graph does later.

Reachability (1) is not asserted from reading — it is measured. With the
default-off probe `SIMPLE_DEBUG_PATTERN_LOWER=1` on a file containing all four
rows above, `bind_subpattern` fires **6** times under the JIT, of which
**3** are `kind=Enum` — the three NESTED struct rows. The top-level
`case Point(a, b)` control never reaches `bind_subpattern` at all (3, not 4).
Same run under `SIMPLE_EXECUTION_MODE=interpreter`: **0**. Flag off: **0**.

### 23. §20 FIXED: `Some((a, b))` bound the nil sentinel, and the cause was slot extraction

§20 recorded this as "binds 0". Re-measured at `e4b4561c8` it binds **3** —
the nil sentinel — which names the cause exactly.

`payload_slot_expr` emitted a bare `rt_enum_payload(subject)`. A `T?` has two
runtime forms: a boxed `Some` enum (literal `Some(x)`, `.at()`) and the raw
migration form (the bare payload) that a natively compiled `T?`-returning
function produces. `rt_enum_payload` answers NIL for the raw form. The
IDENTIFIER binding path in `build_pattern_binding_stmts` already carried the
runtime discrimination for exactly this reason —
`if rt_enum_id(subj) >= 0: rt_enum_payload(subj) else: subj` — but every
NON-identifier sub-pattern under `Some` went through `payload_slot_expr` and did
not. That is why `case Pair((0, b))` over a genuine enum payload has always
passed while `case Some((a, b))` has not: the defect is specific to the
Option dual representation, not to tuples.

Fixed by hoisting the same guard into `payload_slot_expr` itself, keyed on the
outer variant being `Some` with arity 1. It is the shared owner, so the
CONDITION side (`nested_payload_condition`) and the BINDING side get it
together and cannot drift. `bind_nested_payload` was rewritten to delegate to
the same owner instead of rebuilding the extraction by hand, so the guard also
applies at every nesting depth rather than only the top one.

| row | base JIT | fixed JIT | interp (both) | expected |
|---|---|---|---|---|
| `match o: case Some((a, b))`, `o = (5, 8)` | `303` | `508` | `508` | `508` |
| `if val Some((a, b)) = o`, `o = (5, 8)` | `303` | `508` | `508` | `508` |
| `Some((3, 7))` — third value-3 control | `303` | `307` | `307` | `307` |
| `Some(...)` over `nil` | `-1` | `-1` | `-1` | `-1` |

`303` is `3 * 100 + 3`: both slots read the nil sentinel. The value-3 row is
kept precisely because a silent nil answers `303` and cannot answer `307`.

### Fixture

`test/fixtures/compiler/nested_payload_subpattern_depth_matrix.spl` gained 7
rows (30 → 37) and 2 enum/`T?` declarations. Both existing value-3 controls
(`d4_value3_ctrl`, `arr2`) and the live harness sentinel are untouched and still
fire. Non-vacuity, whole file:

| binary | JIT | interpreter |
|---|---|---|
| base `e4b4561c803` | **BADCOUNT 6** | BADCOUNT 0 |
| fixed | **BADCOUNT 0** | BADCOUNT 0 |

`cargo test -p simple-compiler --lib` is **3455 passed / 118 failed** at both
shas, and the 118 failure NAMES `diff` clean — the pre-existing set is
unchanged, not merely the count.

Native is unmeasurable for every row above, for the reason in §21.

### 24. §15 "known gap" FIXED: the shape diagnostic now names a source location

§15 recorded that the `option-pattern-shape` warning "carries no source span, so
a hit names the *run*, not the offending line", and that this had to be closed
before any warn -> error triage. It is closed.

`Pattern` carries no span, but its spanned AST owners do — `MatchArm.span`,
`IfStmt.span`, `WhileStmt.span`. A `current_pattern_span: Option<(line, column)>`
on the `Lowerer` is set by every entry point that owns one (statement `match`
arm, expression `match` arm, `if val`, `elif val`, `while val`) and read by
`report_if_never_option` through a `DiagLocation` carrying file, function, line
and column.

Two deliberate limits, both stated rather than hidden:

* The expression-form `if val` is handed the pattern and condition, not the
  statement, so it has no span. That entry point CLEARS the field rather than
  leaving a previous arm's location in place, and the warning degrades to
  `file (fn name)`. A stale location is worse than none.
* `elif_branches` is `(Option<Pattern>, Expr, Block)` in the AST with no span of
  its own, so an `elif val` hit reports the enclosing `if` statement.

Before / after on the same 4-site probe (3 bare-`int` sites plus a legitimate
`i64?` control), gate `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1`:

```
base   warning[option-pattern-shape]: `Some(...)` pattern (statement form) ...
fixed  warning[option-pattern-shape]: probe/d4_diag.spl:14:9 (fn m_arm): `Some(...)` ...
       warning[option-pattern-shape]: probe/d4_diag.spl:19:5 (fn if_form): ...
       warning[option-pattern-shape]: probe/d4_diag.spl:25:5 (fn elif_form): ...
```

Still 3 warnings, not 4 — the legitimate `i64?` site is not flagged, so the
under-report property of §12 is intact. Gate OFF: 0 warnings and stdout
byte-identical to the gate-ON run, so the diagnostic still changes no behaviour.
Nothing was promoted to an error.

### 25. §18 NOT fixed — root cause located, and it is not in pattern lowering

§18 recorded "`rt_is_some` on a raw `i64?` holding 3 answers false on the JIT".
That is a symptom. The cause is one step earlier and is a REPRESENTATION
collision, measured at `e4b4561c803` on a 6-row probe:

| row | JIT | interpreter | correct |
|---|---|---|---|
| a `fn f() -> i64?: return 3` | **none** | some 3 | some 3 |
| b `fn f() -> i64?: return Some(3)` | some 3 | some 3 | some 3 |
| c `val x: i64? = 3` | **none** | **none** | some 3 |
| d `[3, 9].at(0)` | some 3 | some 3 | some 3 |
| e `val s = Some(3)` | some 3 | some 3 | some 3 |
| f `val x: i64? = 4` (control) | some 4 | **none** | some 4 |

Rows b, d and e are correct on both engines, so the boxed `Some` form is fine
everywhere and `rt_is_some` itself is not wrong: `rt_is_none` tests
`value.is_nil()`, and `NIL` is `(SPECIAL_NIL << 3) | TAG_SPECIAL` = the integer
**3**, while a BOXED int `v` is `v << 3` and can never be 3.

Rows a and c are the defect: an IMPLICIT coercion of a bare scalar into a
declared `T?` slot (a `return` in a `-> T?` function, a `val x: T? = <scalar>`)
leaves the value unboxed. `Some(3)` is then bit-identical to `nil` and no
runtime test can separate them — which is why no fix belongs in pattern
lowering. Fixing it means making the implicit coercion produce the same boxed
form the other three producers already produce, i.e. changing the "raw
migration form" for scalar optionals. That has tree-wide blast radius (every
`??`, `.?`, `.unwrap()` and arithmetic consumer of a `T?`) and touches exactly
the representation the native/stage-4 lane is working in, so it is filed here
with the locus named rather than attempted from a pattern-lowering lane.

Row f is a second, separate finding: the INTERPRETER gets `val x: i64? = 4`
wrong (answers `_`) while the JIT gets it right. That is §13's defect, now
confirmed to be independent of the value 3.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

LIVE, re-reproduced. Bare `val n = 6` then `n.unwrap_or(-99)`, deployed seed, verbatim:
```
jit:         uo=<value:0x6>
interpreter: uo=6
```
Neither is an error, and the two engines still disagree — exactly the reported defect. (Control in the same program: `Option<bool> == true` prints `p1=true` on both engines, so real Option equality is fine on the hosted engines; the defect is the missing type check on a NON-Option scrutinee.)
