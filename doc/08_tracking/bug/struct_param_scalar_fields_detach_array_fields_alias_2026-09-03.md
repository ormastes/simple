# A struct passed to a function is half-copied: scalar fields detach, array fields alias

Filed 2026-09-03. Status: OPEN. Severity: HIGH — silent wrong answers, no diagnostic.

## Summary

Pass a struct to a function and mutate it in the callee. Whether the caller sees
the mutation **depends on the field's type**:

- a **scalar** field write is invisible to the caller (the struct was copied);
- an **array** field mutation IS visible (the array is shared by reference).

So the same struct is simultaneously by-value and by-reference, field by field.
Nothing warns.

## Reproduction (10 seconds, no build)

```simple
struct Box:
    n: i64
    items: [i64]

fn mutate_field(b: Box):
    b.n = 99

fn mutate_array(b: Box):
    b.items.push(7)

fn main() -> i64:
    var b = Box(n: 1, items: [])
    mutate_field(b)
    print "n=" + str(b.n)                 # prints 1   <- write LOST
    mutate_array(b)
    print "len=" + str(b.items.len())     # prints 1   <- push KEPT
    0
```

```
$ src/compiler_rust/target/release/simple run probe.spl
n=1
len=1
```

Verified 2026-09-03 on the Rust seed.

## Why this is expensive rather than merely surprising

Either rule alone is defensible and learnable. The COMBINATION is not: a reader
must know the declared type of every field to predict whether a callee's write
survives. A refactor that changes a field from `i64` to `[i64]` — or the reverse
— silently flips the aliasing of code that never mentioned that field.

Concretely, it cost a full rewrite of `src/lib/common/term/emulator.spl` during
this lane: void mutator helpers (`fn line_feed(s: TermScreen)`) appeared to work
where they touched the cells ARRAY, and silently did nothing where they touched
the cursor/attribute SCALARS. The failure is not a crash and not a type error —
it is a wrong value, produced quietly.

It also interacts badly with purity: a function that LOOKS pure (takes a struct,
returns a new one) can still reach into the caller's struct through an array
field. `term_feed` had to defend against this explicitly by copying the cells
array and only ever replacing cells whole — never `cells[i].ch = ...`, which
would have written through to the caller's screen.

## The workaround now in use, and its cost

Every helper takes the struct and RETURNS it, and callers rebind:

```simple
w = line_feed(w)          # never: line_feed(w)
```

That is correct under both halves of the current behaviour, so it is what the
emulator, the multiplexer (`mux_model.spl`), and `cs_dashboard.spl` all do. The
cost is that a void mutator — the natural way to write this — is a silent
no-op for scalar fields, so the convention has to be followed everywhere by
discipline, with nothing enforcing it.

## What "fixed" looks like

One rule for the whole struct, whichever is chosen, applied to every field:
either the callee sees a full copy (array writes stop propagating) or it sees
the caller's struct (scalar writes propagate). A lint that flags a void function
taking a struct and writing a scalar field would also close most of the exposure
without a semantic change.

## Related

- `.claude/memory` records a "param-detach" observation from 2026-07-18
  (engine2d paints lost through a fn PARAM), reassessed 2026-07-19 as library
  defects rather than a compiler bug. This record is narrower and reproducible
  in 10 lines with no library involved, so the reassessment does not cover it.
- `.claude/rules/language.md` documents "Nested closure capture — can READ outer
  vars, CANNOT MODIFY". That is a different mechanism and does not mention
  struct parameters.

## Not claimed here

That either half is wrong in isolation. The defect is that they disagree, and
that the disagreement is invisible at the call site.
