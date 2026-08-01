# Text slicing at a mid-codepoint boundary: THREE divergent policies, one of them invalid UTF-8

Status: OPEN (evidence + design decision landed; code fix NOT landed — see
"Why no code landed in this pass")
Measured: 2026-08-01

## Summary

Slicing text at a byte offset that falls **inside** a multi-byte codepoint has
**three different behaviours** in this repo, depending on the *spelling* of the
slice and the *engine*. One of them stores genuinely invalid UTF-8.

`print()` masks all three: every case below renders as the same `a<?>` glyph in
a terminal. **Only the integer length distinguishes them.** Never verify this
class by eyeballing printed output.

## Byte-level evidence (PROVED, measured)

Probe string `s = "aé€𝄞z"` — 11 bytes:

```
61 | c3 a9 | e2 82 ac | f0 9d 84 9e | 7a
a     é       €          𝄞           z
```

Codepoint starts at byte offsets 0, 1, 3, 6, 10; end 11.
Mid-codepoint offsets: 2 (in é), 4–5 (in €), 7–9 (in 𝄞).

Measured with the deployed seed at base `67f59397ee1`, default engine
(Cranelift JIT, reaching C `rt_slice`) vs `SIMPLE_EXECUTION_MODE=interpret`:

| expression | interpret `.len()` | default `.len()` | what is actually stored |
|---|---|---|---|
| `s[0:2]`          | 2 | 2 | `61 c3` — **invalid UTF-8**, both engines |
| `s.slice(0,2)`    | **4** | **2** | interp `61 efbfbd` (lossy U+FFFD) / default `61 c3` (**invalid**) |
| `s.substring(0,2)`| **4** | **2** | same divergence as `.slice` |
| `s[0:8]`          | 8 | 8 | `61 c3a9 e282ac f0 9d` — **invalid**, both engines |
| `s.slice(0,8)`    | **9** | **8** | interp lossy / default **invalid** |
| `s.substring(0,8)`| **9** | **8** | interp lossy / default **invalid** |

Aligned controls (`s[0:1]`, `s[0:3]`, `s[0:6]`, `s[10:11]`) are byte-exact and
identical on both engines, so the probe is live and not vacuous. The
interpret-vs-default divergence on `.slice`/`.substring` is itself the
true-positive control proving the two runs really used different engines.

**The length/bytes mismatch is the proof.** For `s[0:2]` the program reports
`len=2` while `print` emits 4 bytes (`61 ef bf bd`): the stored value is the
2 raw bytes `61 c3`, and stdout's sanitizer substitutes U+FFFD on the way out.

### Engine-reachability caveat

`simple compile --native` **fails closed** on any function containing a slice
expression:

```
cannot compile to standalone native binary: 1 function(s) contain constructs
that require the interpreter:  - main: [CollectionOps]
```

So *standalone native* is **UNMEASURABLE** for this defect, exactly as
`match`-on-enum is for `[PatternMatch]`. The "default engine" column above is
the **Cranelift JIT**, which does reach C `rt_slice`. LLVM and the native
backend also route to `rt_slice` (static reading — INFERRED, not run).

## The family (enumerated)

Five independent implementations of "take a text sub-range", no shared helper:

| # | Implementation | Policy at a split codepoint |
|---|---|---|
| 1 | C `rt_slice` — `src/runtime/runtime_native.c:3110` (string branch 3141–3170) | **raw bytes, no validation** — used by Cranelift + LLVM + native |
| 2 | Simple `rt_slice` — `src/runtime/simple_core/core_string.spl:614` (baremetal, hand-mirrored copy) | **raw bytes, no validation** |
| 3 | Rust `"slice" \| "substring"` — `src/compiler_rust/compiler/src/interpreter_method/string.rs:327` | **lossy U+FFFD** (`String::from_utf8_lossy`) |
| 4 | Rust bracket / `Expr::Slice` — `interpreter/expr/collections.rs:441` and ~930 | **raw bytes** (`Value::text_from_bytes`) |
| 5 | C `spl_str_slice` — `runtime.c:311` **and** `runtime_legacy_core.c:182` (duplicated, divergent on negative indices) | **raw bytes**; this is what the *pure-Simple* codegen emits (`src/compiler/10.frontend/core/compiler/cg_expr.spl:783`) |

Adjacent sub-range producers lacking validation: `rt_string_char_at`
(`runtime_native.c:2393` — splits any multi-byte codepoint), `rt_substr`
(`:4160`), `rt_string_replace`, `rt_string_split` (`:3357`),
`spl_str_index_char` (`runtime.c:326`), and the shared sink `rt_string_new`
(`:2046`, bare `memcpy`).

Correct/safe siblings, for contrast: `rt_string_chars` (`:2157`, lead-byte
width table), `rt_lexer_source_slice` (`:6657`, converts char→byte offsets
first), `lexer_struct.spl:214 char_slice` (char-indexed), interpreter
`substr`/`take`/`drop`/`char_at` (char-based — but therefore a *different unit*
from `slice`, a second latent divergence).

A UTF-8 validator **already exists** and is the natural routing point:
`scalar_utf8_validate` / `rt_text_validate_utf8` —
`src/runtime/runtime_simd_utf8.c:185`, declared `runtime.h:1089`. **No slice
path calls it today.**

## Semantics decision: ERROR, not clamp, not lossy

Slicing text across a codepoint boundary has **no correct answer**, so the
operation must refuse rather than fabricate one:

- **Raw bytes** (today's native/JIT/bracket behaviour) produce a value that is
  not text at all; it corrupts comparison, hashing, serialization and any
  downstream consumer, silently.
- **Lossy U+FFFD** (today's interpreter `.slice`/`.substring`) invents a
  character that was never in the input and changes the length. This is
  "silently producing valid-but-wrong text", which the repo rules rank as
  *worse* than erroring.
- **Clamping** to the enclosing boundary silently returns a **different range**
  than the caller asked for, and would still not equal character semantics
  (`s[0:2]` clamped is `"a"`, but under character indexing it means `"aé"`).

Erroring is additionally the only option that is **forward-compatible with the
owner's 2026-07-30 character-alignment decision** (`doc` ref:
text slicing follows Ruby; index units align to CHARACTER). Under character
indexing a mid-codepoint boundary is *unrepresentable*, so an error is exactly
what that migration yields for today's byte-typed callers — and it surfaces
every affected call site instead of hiding it.

Binary data is unaffected: byte arrays take the separate
`RT_CORE_ARRAY_FLAG_BYTES` branch of `rt_slice`, so erroring on *text* does not
break protocol/wire code.

### Rollout constraint (do not skip)

The blast radius is **not yet measured**. ~7,218 owned text-slice call sites
exist; only 31 were ever classified (11 AT RISK), so any count quoted from the
2026-07-31 audit is a *sample, not a census*. Flipping straight to a hard abort
without measuring risks converting a cosmetic glitch into a toolchain crash.
Required sequencing:

1. Route all five implementations through the single existing validator.
2. Run in **counting** mode over a real workload (full test suite + a compiler
   self-build) to enumerate the true call sites that trip it.
3. Fix those sites, **then** flip the default to a hard error.

Step 2 is the gate. It must not be skipped, and the eventual default must be
the error — not a permanently-warning check.

## Why no code landed in this pass

All five implementations sit behind either the C runtime or the Rust seed.
Verifying a change to either requires relinking the seed binary (a cargo build
into the shared working tree), which this lane is explicitly forbidden from
doing (shared clone, ~14 concurrent lanes). Repo precedent is to **revert
rather than ship unverified** compiler/runtime changes, so only the measured
evidence and the design decision land here.

Exact patch points are listed in the family table above; the validator to route
through is `rt_text_validate_utf8` (`runtime_simd_utf8.c:185`).

## Reproduce

Probe (no imports — any import forces a whole-module interpreter fallback and
makes the run silently vacuous):

```
fn dump(tag: text, v: text) -> void:
    print("<" + tag + "|" + v.len().to_text() + "|" + v + ">")

fn main() -> void:
    val s = "aé€𝄞z"
    dump("bracket_ctl", s[0:3])       # control, must be len 3
    dump("bracket_cut", s[0:2])       # splits é
    dump("slice_cut", s.slice(0, 2))
    dump("substring_cut", s.substring(0, 2))
```

Run once bare and once with `SIMPLE_EXECUTION_MODE=interpret`, redirect stdout
to a file, and `xxd` it. Compare the **lengths**, not the glyphs.

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` (same "native container op is
  silently wrong" shape)
- `byte_at_reads_zero_from_slice_result_2026-07-28.md`
- `bracket_slice_byte_index_survey_2026-07-29.md` and fix passes 1–6
- `text_find_native_exposure_audit_2026-07-31.md`
