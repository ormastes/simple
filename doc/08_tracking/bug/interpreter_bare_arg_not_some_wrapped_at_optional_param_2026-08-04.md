# Interpreter does not Some-wrap a bare argument at a `T?` parameter — `case Some(x)` matches nothing and the whole `match` falls through

- **Filed:** 2026-08-04
- **Status:** OPEN
- **Severity:** high — silent wrong behaviour, and a corpus-wide false-green generator
- **Engines:** interpreter only. The JIT is correct.
- **Blast radius:** 1,762 `case Some(` sites across 423 `.spl` files under `src/`.

## Summary

When a function declares `p: T?` and the caller passes a **bare `T`** (not an
explicit `Some(...)`), the interpreter binds the raw value rather than wrapping
it in `Some`. A subsequent `match p:` with `case Some(n)` / `case None` then
matches **neither arm**. There is no error and no default arm: execution simply
continues past the `match` into whatever statement follows.

`nil` is handled correctly — `case None` matches in both engines. Only the
present-value arm is affected.

The JIT wraps correctly, so the defect is invisible in a plain `simple run`
of a file that JIT-compiles. `src/app/test_runner_new/test_runner_single.spl`
forces `SIMPLE_RUNTIME_MODE=interpreter` and `SIMPLE_EXECUTION_MODE=interpret`
for every spec child, so **every spec in this repo runs on the broken path**.
No spec can currently observe a `case Some(x)` arm on a `T?` parameter that
received a bare value.

## Minimal repro

`test/fixtures/optional_arg_coercion/opt_min_main.spl` (committed with this report):

```
class Box:
    val tag: text

fn m_box(p: Box?) -> text:
    match p:
        case Some(n):
            return "Some:" + n.tag
        case None:
            return "None"
    "FELL_THROUGH"
```

with `m_box(Box(tag: "x"))`, `m_box(nil)`, and the same shape for `i64?` and
`text?`. One binary, one file, one variable — the execution mode:

```
$ simple run test/fixtures/optional_arg_coercion/opt_min_main.spl
MAIN_box=Some:x
MAIN_box_nil=None
MAIN_int=Some:7
MAIN_text=Some:hi

$ SIMPLE_RUNTIME_MODE=interpreter SIMPLE_EXECUTION_MODE=interpret \
    simple run test/fixtures/optional_arg_coercion/opt_min_main.spl
MAIN_box=FELL_THROUGH
MAIN_box_nil=None
MAIN_int=FELL_THROUGH
MAIN_text=FELL_THROUGH
```

The `FELL_THROUGH` string is the statement *after* the `match`. It is reached
because no arm was taken — not because a `None` arm returned it.

It is not a closure defect, though it looks like one at first: adding any
lambda to the file makes the driver refuse to JIT (`the JIT closure ABI does
not tag-box lambda arguments or results`) and fall back to the interpreter, at
which point even a call from `fn main` starts returning `FELL_THROUGH`. The
axis is the engine, not the call site.

## Observed production consequence

`src/lib/gc_async_mut/gpu/browser_engine/style_block_resolve.spl`,
`selector_matches`, lines 39-43:

```
        match parent:
            case Some(parent_node):
                return simple_selector_matches(parent_selector, parent_node, 1, 1)
            case None:
                return false
```

Under the interpreter neither arm runs, so control reaches the *descendant*
combinator branch below and the function returns `true` from the
"any-ancestor" path. A strict child combinator therefore degrades into
descendant-like matching — precisely the failure the code's own comment says it
exists to prevent ("keep this strict instead of letting whitespace tokenization
degrade it into descendant-like matching").

Demonstration, same binary, same file:

```
selector_matches("p > span", <span>, <div parent>, 1, 1)
  fn main        -> false   (correct: the parent is a div, not a p)
  spec `it` body -> true    (wrong)
```

`test/fixtures/optional_arg_coercion/selector_child_combinator_main.spl`
reproduces it on one binary by switching only the execution mode:
`parent_mismatch=false` under the JIT, `parent_mismatch=true` under the
interpreter, with `no_parent` (the `case None` arm) correct in both.

## Coverage consequence

Line 41 of `style_block_resolve.spl` (`return
simple_selector_matches(parent_selector, parent_node, 1, 1)`) is **not
coverable by any spec** while this defect stands. It is not untested code and
it is not unreachable by construction; it is blocked by an engine defect. It is
excluded from the "reachable" denominator on that basis in
`style_block_resolve_selectors_spec.spl`, with this document as the reason.

## Where to look

Argument binding for a declared `T?` parameter in the interpreter's
function-entry path — `src/compiler_rust/compiler/src/interpreter_call/core/`
(`execute_function_body` and the `exec_function_*` helpers that build the local
environment). The JIT performs the coercion; the interpreter's equivalent step
does not. Note that a bare `nil` already produces a value the `case None` arm
recognises, so only the present-value wrap is missing.

A fix must also decide what a `match` with no matching arm should do. Falling
through silently is what turns a type error into a wrong answer here; an
exhaustive `match` over `T?` that matches nothing should be a hard error, not a
no-op.
