# Seed interpreter regression: JS-engine statement dispatch broken — `for is not defined` / `__simple_i is not defined` / `typeof`-of-undefined throws

- **Date:** 2026-08-15
- **Status:** OPEN — seed (Rust bootstrap) interpreter regression. Not a source change.
- **Severity:** High — silently breaks the in-process JS engine (`BrowserSession.open_html`, page-script execution, ES5 conformance) whenever the affected seed is the active `bin/simple`.
- **Owned scope:** compiler seed (`src/compiler_rust`), stdlib JS engine (`src/lib/*/js/engine`, `src/lib/gc_async_mut/web`).

## Symptom

Running the browser / JS specs under the seed rebuilt around origin/main wave
`28153fd430d` produces runtime `ReferenceError`s from the Simple-implemented JS
interpreter:

```
[WARN] [browser-session] ReferenceError: for is not defined
[WARN] [browser-session] ReferenceError: __simple_i is not defined
[WARN] [es5-conformance] ReferenceError: if is not defined      (×167 in one run)
[WARN] [es5-conformance] ReferenceError: while/switch/try/void/delete is not defined
[WARN] [test]           ReferenceError: x / y / n is not defined
```

The originally-reported `typeof require` → `ReferenceError: require is not
defined` (typeof of an undefined identifier throwing instead of yielding
`"undefined"`) is the same failure class: the seed mis-executes the JS engine's
statement-kind dispatch and variable binding, so statement keywords (`for`,
`if`, `while`, …) and desugar temporaries (`__simple_i`) fall through to the
identifier-lookup path and throw.

## This is a SEED regression, not a source change (byte-identical evidence)

The JS-engine and web source trees are **byte-identical** across the entire
wave. Git tree object SHAs at `a155bff913f~1` (pre-wave), `28153fd430d` (wave
head), and `38608afcc5e` (current origin/main tip):

| path | pre-wave | wave head | current |
|------|----------|-----------|---------|
| `src/lib/gc_async_mut/js/engine`  | `7cf576378a12…` | `7cf576378a12…` | `7cf576378a12…` |
| `src/lib/gc_async_mut/web`        | `af4fe04fbe28…` | `af4fe04fbe28…` | `af4fe04fbe28…` |
| `src/lib/nogc_async_mut/js/engine`| `0543735d8996…` | `0543735d8996…` | `0543735d8996…` |

Identical trees, changed behavior ⇒ the trigger is the seed binary, which was
redeployed around this wave (`bin/release/x86_64-unknown-linux-gnu/simple`,
Rust bootstrap seed — self-identifies as "bootstrap seed only").

## Suspected trigger commit

`a155bff913f` — *"fix(engine2d): interpreter nested field-assign, SIMD span
write-back, class-name collisions; GPU-offload render-diff + web offload specs"*
is the **only** commit in the wave range (`a155bff913f~1..28153fd430d`) that
touches `src/compiler_rust` / `src/compiler`. It rewrites the interpreter
statement/expression executor heavily:

```
src/compiler_rust/compiler/src/interpreter/node_exec.rs | 355 +++++++--
src/compiler_rust/compiler/src/value.rs                 |  43 +++
src/compiler_rust/compiler/src/value_bridge.rs          | 273 +++----
src/compiler_rust/compiler/src/value_impl.rs            |  13 +-
```

`node_exec.rs` is the node executor that evaluates `for`/`if`/`while` statements
and resolves identifiers; a regression there matches the observed failure shape
exactly (statement keywords and the `__simple_i` for-desugar temporary resolving
as undefined identifiers). This is the prime suspect; the second interpreter
touch in the wider window, `79af7194357` (bulk `arr.write_span`), does not touch
statement/identifier evaluation and is a weaker candidate. Bisecting the seed
across these two commits would confirm.

> NOTE: all runs below are **diagnostic only**, executed on the Rust bootstrap
> seed. Per project rules the Rust seed is never release evidence.

## Minimal repro

`BrowserSession.open_html` with a trivial DOM-mutating `<script>`:

```
var session = BrowserSession.new()
val html = "<html><body><div id='g'>x</div>" +
  "<script>document.body.innerHTML='<div id=\"g\">ok</div>';</script></body></html>"
session.open_html("https://example.test/t.html", html)
```

emits `ReferenceError: for is not defined` / `__simple_i is not defined` and the
rendered document is the empty `about:blank` skeleton (script never applied).
The same is reproduced directly by
`test/01_unit/browser_engine/browser_script_execution_spec.spl`.

## Blast radius (each spec run once, diagnostic seed)

| spec | verdict | same signature? |
|------|---------|-----------------|
| `test/01_unit/browser_engine/browser_script_execution_spec.spl` | FAIL 0/4 | yes — `for` / `__simple_i` not defined |
| `test/03_system/feature/js/interpreter_vars_spec.spl` | FAIL 12/21 | yes — `for`, plus `x`/`y`/`n` var-binding |
| `test/03_system/feature/js/es5_conformance_spec.spl` | FAIL 38/54 | yes — broad: `if`(×167)/`for`/`while`/`switch`/`try`/`void`/`delete` not defined |
| `test/01_unit/lib/js/typeof_builtin_introspection_spec.spl` | PASS 5/5 | control — standalone `js.types` engine path unaffected |
| `test/01_unit/browser_engine/browser_renderer_spec.spl` | FAIL 8/10 | no — 2 failures, no `is not defined` signature (unrelated to this regression) |

The `typeof_builtin_introspection` PASS shows the regression is in the seed's
execution of the JS-engine statement/var machinery, not universal; the affected
path is the one BrowserSession and the ES5/interpreter conformance suites drive.

## Recommended robustness fixes (in the gc JS engine)

Independent of fixing the seed, harden the gc engine so these constructs cannot
mis-resolve:

1. **`typeof` of an undefined identifier must yield `"undefined"`**, never throw
   a `ReferenceError` — per ES semantics `typeof undeclared === "undefined"`.
   The `typeof` unary path must intercept the bare-identifier operand before the
   general identifier-lookup that throws.
2. **For-loop desugar var binding** — the `__simple_i` (and analogous) loop
   temporaries must be bound in the loop scope before the body/condition
   executes, so `for` and its induction variable are never surfaced as
   free identifiers.

A parallel pure-Simple robustness fix for these two is in progress in another
agent session.

## Follow-up

- Bisect the seed between `a155bff913f~1` and `28153fd430d` (only `a155bff913f`
  is compiler-touching) to pin the exact `node_exec.rs` hunk.
- Add a seed-level regression guard executing a `for`-loop + `typeof undeclared`
  through the interpreter so a rebuild that breaks statement dispatch fails CI
  before it is deployed as `bin/simple`.

## Resolution (2026-08-15) — fixed in pure Simple, seed-robust

Root cause refined by the fix pass: the nogc subset parser
(`js_parse_program_subset`, used by `JsRuntime.eval`) never handled `for` /
`while` / `if` / block statements — a C-style `for (var __simple_i=0; …)` fell
through to expression parsing and its header was evaluated as bare identifier
lookups (`for`, `__simple_i`). On the pre-08:26 seed that fall-through was a
tolerated warning; the redeployed seed (trigger `a155bff913f`, node_exec.rs
statement/identifier rewrite) turned the same fall-through into a fatal
ReferenceError that aborted `BrowserSession` runtime init. Two spec-correctness
gaps compounded it: `typeof <unresolved>` propagated the throw instead of
yielding `"undefined"`, and a function-typed DOM mutation field was called
without binding to a local.

Fixed additively (no-op under the self-hosted compiler, corrective under the
seed), all pure Simple:
- `src/lib/nogc_sync_mut/js/engine/parser.spl` — real `for` (C-style + for-in/of
  + malformed guard), `while`, `if`/`else`, and block parsing.
- `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl` — `typeof` of an
  unresolved identifier returns `"undefined"`.
- `src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl` — bind the
  closure field to a local before invoking.

`browser_script_execution_spec` 4/4 and `browser_animation_clock_spec` 2/2
green on the current origin seed (diagnostic evidence — a self-hosted redeploy
should reconfirm). The broader seed statement-dispatch regression (es5_conformance
38/54, interpreter_vars 12/21) remains a SEED defect for the seed/Stage-4 owner;
the recommended seed-level CI guard above still applies.
