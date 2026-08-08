# Paren-less container accessors silently drop the whole module out of JIT

- **Filed:** 2026-08-08
- **Status:** OPEN (fence landed; upstream fix not done)
- **Severity:** High — silent ~100-1000x slowdown, correct output, no diagnostic
- **Fence:** `scripts/check/check-no-jit-module-drop.shs`

## Summary

A paren-less accessor on a builtin container — `.length`, `.len`, `.size`,
`.empty`, `.chars`, `.first`, `.last`, `.capacity` — parses as a **field
access**. There is no HIR lowering for it, so `hir/lower/expr/access.rs:400`
raises:

```
cannot infer field type while lowering <fn>: struct 'Array' field 'length'
```

(also `struct 'String'`, `struct 'Dict'`).

The two lanes disagree, and that is the whole defect:

| lane | behaviour |
|------|-----------|
| `bin/simple compile <f>` | **rc=1**, hard error, names struct + field |
| `bin/simple run <f>` (JIT) | **rc=0**, prints the correct value, whole enclosing module silently dropped to the tree-walk interpreter |

Measured 2026-08-08 on `bin/simple` (currently the Rust seed — it self-reports
`this Rust-built Simple binary is a bootstrap seed only`):

```
$ bin/simple run  scratch/bad.spl      # val xs = [1,2,3]; print xs.length
3                                       # rc=0, no diagnostic at all
$ bin/simple compile scratch/bad.spl
error: ... cannot infer field type while lowering main: struct 'Array' field 'length'
```

All eight family members were confirmed to raise it under `compile`:

```
xs.length   -> struct 'Array'  field 'length'
s.length    -> struct 'String' field 'length'
d.length    -> struct 'Dict'   field 'length'
xs.first    -> struct 'Array'  field 'first'
xs.empty    -> struct 'Array'  field 'empty'
s.chars     -> struct 'String' field 'chars'
xs.size     -> struct 'Array'  field 'size'
```

## Why `.length` accumulated the most sites

`.length` is the only member the **interpreter** both accepts and evaluates
correctly. `.size` and `.empty` also die at runtime (`undefined field: unknown
property or method 'size' on Array`), so they self-report the moment anyone runs
the code. `.length` prints the right number and says nothing. That asymmetry is
why it is the dominant member of the class.

## Finding 1 (premise correction): `SIMPLE_JIT_STRICT=1` does NOT harden this

This was believed to be an existing mitigation that merely nothing invoked. It
is not. `SIMPLE_JIT_STRICT=1` only turns a fallback into a hard error for errors
routed through `jit_strict_fallback_error` (`driver/src/exec_core.rs:1261`) —
i.e. HIR/MIR `LowerError` and, separately, unresolved externs in
`codegen/jit.rs`. Only those messages carry the `SIMPLE_JIT_STRICT:` prefix that
`run_file_with_args` tests for:

```rust
if jit_err.contains("SIMPLE_JIT_STRICT:") { return Err(jit_err); }
// else: eprintln!("[INFO] JIT compilation failed, falling back to interpreter: ...")
```

The accessor family is caught **earlier**, at the semantic gate
(`pipeline/lowering.rs`), whose message is never tagged. So the `contains` test
is false and the driver falls back to the interpreter **regardless of strict
mode**. Verified directly:

```
$ SIMPLE_JIT_STRICT=1 bin/simple run scratch/t4.spl     # xs.empty
[INFO] JIT compilation failed, falling back to interpreter: semantic: undefined field: unknown property or method 'empty' on Array
```

Strict was set and it still fell back. Same for a struct with a genuinely absent
field (`class P has no field named y`). In every probe attempted, the
`[jit-fallback]` marker was **never** emitted — every observed drop went through
the untagged `[INFO]` path instead.

**Consequence:** a `run`-based fence for this class would be vacuous. That is why
the landed fence drives `compile`.

## Finding 2: the drop message does not name the source file

`[jit-fallback] {kind}: {err}` and the `[INFO]` variant both name struct and
field but not the file. The fence works around this by compiling **one file at a
time** and attributing from the loop variable. Upstream, the message should
carry the path and span.

## Recommendation for the upstream fix

**Reject at semantic analysis, uniformly across all lanes. Do not lower them as
sugar, and do not try to reject them in the parser.**

1. **Not the parser.** `recv.length` is legitimate syntax — genuine `length`
   struct fields exist in this tree (`SvimPiece.length`, `RefcBinary ref.length`)
   and are declared in files other than the use site. The parser has no type
   information and cannot tell them apart. Scope here is not statically
   decidable; that is also why grep gives only an upper bound (a textual sweep
   produced 254, then 165, both over-reporting).

2. **Not sugar either.** Lowering `.length` to `.len()` would create two
   spellings for one operation and make paren-less `.len` mean something
   different from `.len()`. Worse, on a `Dict` receiver it would silently route
   into `Dict.len()`, which returns **−1** under native codegen
   (`doc/07_guide/language/dict_native_pitfalls.md`). Sugaring would convert a
   loud compile error into a wrong answer.

3. **Do this:** in the semantic gate, when a field access resolves to a builtin
   container (`Array` / `String` / `Dict`) and the field name matches a known
   method, emit a hard, actionable error naming file, line, and the fix
   (`use .len()`). It is already a hard error in the `compile` lane — the fix is
   to make the `run`/JIT lane agree instead of silently degrading.

4. **Independently, close the strict-mode hole:** route the semantic-gate
   failure through `jit_strict_fallback_error` so `SIMPLE_JIT_STRICT=1` actually
   covers the path where these land, and add the source path to the message. As
   it stands, strict mode advertises coverage it does not have — the same
   "advertised coverage that does not exist" pattern called out in
   `scripts/check/check-aot-lane-fences.shs`.

## Fence

`scripts/check/check-no-jit-module-drop.shs` — fail-closed, exit 0/1/2 with a
verdict line stating how many modules were actually examined. It drives
`bin/simple compile` (non-executing, per-file attributable), runs a fatal
bidirectional `--selftest` before every scan, and treats an empty roster, an
unmeasurable file, and a non-firing selftest as ERROR rather than PASS.

Deliberately **not** wired into any pre-commit/pre-push hook: a per-file compile
over the candidate roster costs ~15-20 minutes and this checkout is shared by
about ten concurrent sessions.

### Injection test (both directions, on a real tree file)

```
src/lib/bitwise_utils.spl, unmodified   -> PASS — 1 module(s) checked, 0 drops
+ fn __injected_probe(elements: [i64]) -> i64: return elements.length
                                        -> FAIL — 1 file(s) checked, 1 drop
   DROP  src/lib/bitwise_utils.spl  struct 'Array' field 'length'
plant removed, blob back to 340ba81     -> PASS — 1 module(s) checked, 0 drops
```

The fence names the offending file, and it was shown to fire on a real tracked
source file rather than only on its own fixture.

## Incidental: `git checkout -- <path>` emptied a tracked file

While reverting the injection plant, `git checkout -- src/lib/bitwise_utils.spl`
restored the file to the **empty blob** `e69de29`, destroying 35 lines. The
content was recovered from a pre-edit copy and verified back to
`340ba81fdb0e87da87b2024e417eb83218bfcd90`. This is the documented empty-blob
trap in this checkout's index; do not use `git checkout --` to revert here
without pinning and re-verifying the expected blob SHA afterwards.
