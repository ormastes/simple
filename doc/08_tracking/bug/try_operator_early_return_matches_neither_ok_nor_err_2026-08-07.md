# `?` early-return produces a value that matches neither Ok nor Err (seed)

- **Status:** OPEN
- **Found:** 2026-08-07
- **Area:** `?` (try) operator — seed runtime, observed via `bin/simple run`
- **Severity:** high — an error propagated with `?` is silently LOST at the call
  site; the caller's `match` falls through every arm and execution continues

## Symptom

When a function propagates a failure with `?`, the `Result` the caller receives
matches **neither** `case Ok(...)` nor `case Err(...)`. No arm runs, nothing is
printed, and no error is raised — the call simply evaporates.

Minimal repro (seed interpreter, rc=0):

```simple
fn inner_tuple(bad: bool) -> Result<tuple, text>:
    if bad:
        return Err("boom")
    Ok(("payload", 1))

fn outer_try(bad: bool) -> Result<text, text>:
    val p = inner_tuple(bad)?
    return Ok(p.0)

fn outer_match(bad: bool) -> Result<text, text>:
    match inner_tuple(bad):
        case Ok(p): return Ok(p.0)
        case Err(e): return Err(e)

fn show(label: text, r: Result<text, text>):
    match r:
        case Ok(v): print(label + " OK:[" + v + "]")
        case Err(e): print(label + " ERR:[" + e + "]")

fn main():
    show("try   good:", outer_try(false))
    show("try   bad :", outer_try(true))
    show("match good:", outer_match(false))
    show("match bad :", outer_match(true))
```

Actual output — the `try bad` line is **absent entirely**:

```
try   good: OK:[payload]
match good: OK:[payload]
match bad : ERR:[boom]
```

Expected: `try bad : ERR:[boom]`, identical to `match bad`.

The success path through `?` is fine; only the error path is broken. The
hand-written `match` is correct in both directions, which isolates the fault to
`?` rather than to `match`, to `Result`, or to the tuple payload.

## Why this matters

`.claude/rules/language.md` makes `Result<T, E>` + `?` **the** sanctioned error
mechanism ("no try/catch/throw keywords — by design"). A `?` that drops errors
means every function using the sanctioned idiom can silently swallow failures.
It is also a fail-open verification trap: a probe that only exercises the happy
path sees `?` working perfectly.

## How it was found

While repairing `decode_chunked` (see
`decode_chunked_malformed_size_silently_truncates_body_2026-08-06.md`),
`http1.decode_chunked` was first written as:

```simple
val pair = decode_chunked_with_trailers(encoded)?
return Ok(pair.0)
```

Its two error probes printed blank lines while the success probes were correct.
Rewriting the body as an explicit `match` made all cases pass. That workaround
is in the shipped code and is marked here rather than being normalised silently.

## Fix direction

Start by inspecting the desugaring of `?` in the seed and comparing the value it
early-returns against the one the explicit `match` arm constructs.

**No root cause is claimed here.** What was observed is the symptom and its
isolation: the success path through `?` is correct, the hand-written `match` is
correct in both directions, and only the `?` error path is lost. The
desugaring was not read, so any statement about *why* would be speculation —
deliberately left out so the next lane is not pointed down an unverified path.

Once fixed, revert `http1.decode_chunked` to the `?` form and re-run the probe
above; it must print `try bad : ERR:[boom]`.
