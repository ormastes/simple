# The "278 orphaned methods in inert cross-tier impl blocks" finding is REFUTED

Date: 2026-08-05
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## What was claimed

A census recorded **16 `impl JsInterpreter` blocks / 278 methods** in
`src/lib/gc_async_mut/js/engine/` and `src/lib/nogc_async_mut/js/engine/` as
**silently inert dead code**, on the theory that an `impl <Class>:` block placed
in a stdlib tier that declares `<Class>` in none of its own modules cannot
resolve. `scripts/check/check-inert-cross-tier-impl.shs` encoded that theory as
a ratcheting guard with those 16 paths as its baseline.

The recommended remedy was to delete the 278 methods as duplicates of the
copies in `nogc_sync_mut`, where `class JsInterpreter` is declared.

## Why it is wrong

Deleting them would have been a **regression**. Two sabotage pairs, run against
`bin/simple` (the Rust seed currently deployed at
`bin/release/x86_64-unknown-linux-gnu/simple`), show the "inert" blocks
executing.

### Pair 1 — `_native_node_require`

Spec: `test/01_unit/lib/common/web/browser_session_node_host_gc_async_spec.spl`,
which imports the extension module explicitly
(`use std.gc_async_mut.js.engine.interpreter_native.*`).

| arm | sabotage | verdict |
|-----|----------|---------|
| baseline | none | `Results: 1 total, 1 passed, 0 failed` |
| A | early `return JsValue.String(v: "SABOTAGE_GC_ASYNC")` in **`gc_async_mut`**`/js/engine/interpreter_native.spl` | `1 total, 0 passed, 1 failed` — `expected  to equal yes` |
| B | same edit in **`nogc_sync_mut`**`/js/engine/interpreter_native.spl` | `1 total, 1 passed, 0 failed` |

Arm A is a behavioural assertion failure, not a compile error. The
supposedly-inert `gc_async_mut` copy is what ran; the `nogc_sync_mut` copy did
not.

### Pair 2 — `_native_fetch` credentials default

Spec: `test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl`
(rewritten by this lane, see below), which reaches the engine through
`BrowserSession`.

| arm | sabotage | verdict |
|-----|----------|---------|
| baseline | none | `Results: 5 total, 5 passed, 0 failed` |
| A | `var credentials = "SABOTAGED"` in **`gc_async_mut`** | `5 total, 5 passed, 0 failed` — did NOT bite |
| B | same edit in **`nogc_sync_mut`** | `5 total, 3 passed, 2 failed` |

## The correct model

Both copies are live. **Which copy wins depends on the import path of the
calling module**, not on which tier declares the class:

- a module that imports the extension module by explicit tier path
  (`use std.gc_async_mut.js.engine.interpreter_native.*`) gets the
  `gc_async_mut` methods;
- a module that reaches the engine through the tier-agnostic `std.js.engine.*`
  / `BrowserSession` path gets the `nogc_sync_mut` methods.

A third arm confirms the split: sabotaging `gc_async_mut`'s
`_native_node_require` left `test/03_system/feature/js/node_api_conformance_spec.spl`
unchanged at `275 total, 271 passed, 4 failed`, so the tier-agnostic path does
not resolve to `gc_async_mut` either.

So the guard's predicate — *class not declared in this tier ⇒ block is inert* —
is **unsound**. It reported live, executing code as dead, and its 16-path
baseline was a list of false positives. A ratchet whose baseline is false
positives is worse than no guard: it manufactures confidence, and here it would
have justified deleting working code. `scripts/check/check-inert-cross-tier-impl.shs`
is therefore deleted rather than re-baselined. It was standalone — no script,
pre-commit hook or CI workflow referenced it.

## The real defect (still open)

The genuine problem in this family is **cross-tier duplicate method definitions
of one class, dispatched by importer module path**:

- 275 of the 278 method names exist under the same name in the corresponding
  `nogc_sync_mut` file, with **divergent bodies** — `nogc_sync_mut`'s
  `interpreter_native.spl` is 9,118 lines against `gc_async_mut`'s 1,501 and
  `nogc_async_mut`'s 694.
- 3 method names exist only in the `gc_async_mut` cluster
  (`_consume_response_body`, `_get_internal_object_property`,
  `_set_internal_object_property`) and are called only from inside it.
- The one method the original report cited as evidence of cost,
  `cancel_pending_async_fetches`, does exist twice — at
  `gc_async_mut/js/engine/interpreter_async.spl:134` and
  `nogc_sync_mut/js/engine/interpreter.spl:433`. The lane that hit it did not
  hit an *inert* method; it hit the wrong one of two live copies.

Deduplicating toward one tier is real work with a large blast radius (the
bodies differ, and `src/lib/gc_sync_mut/js/engine/*.spl` facades re-export the
`gc_async_mut` modules). It needs its own lane, a full JS-engine spec sweep,
and a self-hosted binary rather than the seed. It must NOT be done by bulk
deletion on the strength of the retired guard.

## Collateral fixed in the same change

Two specs "covered" these files by reading them as **text**
(`rt_file_read_text` + `to_contain`) — green regardless of behaviour, and red
for any pure refactor. Both are now executing specs:

| spec | before | after |
|------|--------|-------|
| `test/01_unit/lib/gc_async_mut/js/interpreter_native_buffer_guard_spec.spl` | 2 text-grep examples | 3 executing examples driving JS through `JsParser` + `JsInterpreter.execute` |
| `test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl` | 1 text-grep example over 3 tier copies | 5 executing examples driving `BrowserSession.eval_script` + `take_pending_request()` |

Both were sabotage-verified. Inverting the `Buffer.isBuffer` empty-argument
guard took the first from `3 total, 3 passed` to `3 total, 2 passed, 1 failed`;
corrupting the credentials default took the second from `5 total, 5 passed` to
`5 total, 3 passed, 2 failed`. The first spec additionally had no
`use std.spec.*` at all before this change.
