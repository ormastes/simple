# `text.len()`/`substring` are byte-indexed but `text[i]` is char-indexed

Status: OPEN — language/stdlib defect, wider than the caret lane that found it
Found: 2026-08-30, via `caret --provider claude_cli` crashing on a claude CLI
warning that contained one em dash.

## The disagreement

```
fn main() -> ():
    val d = "a—b"
    print("len={d.len()}")            # 5   <- BYTES
    print("sub(1,2)=[{d.substring(1,2)}]")  # replacement char <- BYTES (splits the em dash)
    print("d[1]=[{d[1]}]")            # —   <- CHARS
    return ()
```

`len()` and `substring()` count UTF-8 bytes. `[]` counts characters, and
bounds-checks against the CHARACTER count. For any string containing a
non-ASCII byte the two disagree, and the gap is the number of continuation
bytes.

## Why it is not cosmetic

The idiomatic hand-written scanner in this tree is

```
val n = s.len()
while i < n and _is_ident_char(s[i]):
```

which is `while i < <byte count>` driving `s[i]` bounds-checked against
`<char count>`. On any non-ASCII input it runs past the end and traps:

```
error: semantic: string index out of bounds: index is 43 but length is 43
```

43 is the char count; the loop was bounded by the 45-byte length. Note the
message reads as a contradiction ("index is N but length is N") precisely
because the two Ns are in different units — that is itself a diagnostic bug
worth fixing alongside.

## Reproduction through the product

```
$ bin/simple run src/app/llm_caret/main.spl --provider claude_cli \
    --prompt "Say hello in three words." --plain
error: semantic: string index out of bounds: index is 691 but length is 691
  (preview="claude CLI exited with code 1: Warning: Advisor disabled — b")
```

The em dash is in the *upstream CLI's own warning text*, so caret cannot avoid
it by sanitising its inputs. `src/app/llm_caret/redact.spl` is the crash site
(`_run_key_chars` / `_run_ident_chars` / `_run_non_space` / `_run_upper_digit`,
all `while i < n and ... s[i]`), and redact runs on every CLI error path — so
a non-ASCII byte anywhere in a subprocess's stderr takes the process down
instead of being redacted.

## Blast radius

Every hand-written scanner that pairs `.len()` with `[]`. This is a common
shape in the compiler, the linter, and the JSON/SDN readers, not a caret-local
idiom. Any one of them is a latent trap on non-ASCII input.

## Fixing it is an architecture decision, not a bug fix

Two coherent resolutions, with opposite costs:

- make `[]` byte-indexed — self-consistent, cheap, but indexing then yields
  fragments of characters rather than characters;
- make `len()`/`substring()` char-indexed — correct Unicode, but O(n) indexing
  and a very wide blast radius across existing byte-oriented callers.

Deliberately NOT chosen here: picking one silently would change the meaning of
existing code across the tree. This needs an owner's decision.

## Interim

`redact.spl` should be made safe on its own (bound its scans by the same unit
it indexes in) so that a subprocess's non-ASCII stderr cannot crash caret,
independently of how the language question is settled.
