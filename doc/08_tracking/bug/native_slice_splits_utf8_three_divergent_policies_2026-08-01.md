# Text slicing at a mid-codepoint boundary: THREE divergent policies, one of them invalid UTF-8

Status: RESOLVED 2026-08-21 for the ENGINE DIVERGENCE — the three policies are
now one. `.slice()`/`.substring()` in the interpreter preserve RAW BYTES, the
same as bracket `s[i:j]` on every engine and the same as `rt_slice` on
JIT/native, so the spelling of the slice no longer changes the answer and the
engines no longer disagree. See "Resolution (2026-08-21)" at the end.
Stage 1 (counting mode) LANDED `2ca6b4da3a9`; stage 2 (blast-radius
measurement) MEASURED, see "Stage 2". Stage 4 (flip a mid-codepoint slice to a
hard ERROR) remains **deferred** and is a SEPARATE question from the divergence
— the ~891 byte-stepping scanner call sites that justify deferring it are
unchanged by this fix. Sections below describing the pre-fix three-way split are
kept as the historical record; read them as "before 2026-08-21".
Measured: 2026-08-01

**Re-verified 2026-08-07, unchanged.** Ran the "Reproduce" probe below (`s =
"aé€𝄞z"`, no imports) via `bin/simple run` (default engine — confirmed real
Cranelift JIT engagement via `cranelift_jit::backend` "defining function" log
lines, not a fallback) and again with `SIMPLE_EXECUTION_MODE=interpret`.
Byte-exact reproduction of the original table:

| expression | interpret `.len()` | default (JIT) `.len()` | bytes stored |
|---|---|---|---|
| `s[0:3]` (aligned control) | 3 | 3 | `61 c3a9` — valid, both engines |
| `s[0:2]` (splits é) | 2 | 2 | `61 c3` — **invalid UTF-8**, both engines |
| `s.slice(0,2)` | **4** | **2** | interp lossy U+FFFD (`61 efbfbd`) / default raw `61 c3` (**invalid**) |
| `s.substring(0,2)` | **4** | **2** | same divergence as `.slice` |

All three policies (raw-bytes JIT/native/bracket, lossy-U+FFFD interpreter
`.slice`/`.substring`, and the aligned byte-for-byte agreement on safe
boundaries) still hold exactly as measured on 2026-08-01/02. No regression, no
fix landed since. `test/01_unit/bugs/text_slice_substring_spec.spl` §"Test
Group 8: Multi-byte / UTF-8" already pins the interpreter-side lossy-U+FFFD
behavior end to end and is GREEN (`Results: 76 total, 76 passed, 0 failed`,
re-run 2026-08-07) — it does not and cannot cover the JIT/native raw-bytes
policy, because `bin/simple test` hard-defaults to the interpreter engine
(`.claude/rules/testing.md`); there is no test-harness path that drives
`s[0:2]`-style bracket slicing through Cranelift/LLVM/native to pin the
invalid-UTF-8-bytes behavior as a spec assertion. That gap is inherent to the
harness, not a missing spec.

No further action taken this pass: the existing root-cause analysis, the
five-implementation family table, the byte-accessor (`byte_at`) prerequisite,
and the "do not flip yet" recommendation below are all still current and
correct. Patching the primitive (validate+adjust or fail-closed) would still
break the ~891 remaining byte-stepping scanner call sites documented under
"Stage 3 migration" — that risk has not changed since 2026-08-02, so no code
change was made in this pass; see that section for the migration plan that
must land first.

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

~7,218 owned text-slice call sites exist statically; only 31 were ever
classified (11 AT RISK), so any count quoted from the 2026-07-31 audit is a
*sample, not a census*. Flipping straight to a hard abort without measuring
risks converting a cosmetic glitch into a toolchain crash. Required sequencing:

1. Route all five implementations through the single existing validator.
   — **DONE**, `2ca6b4da3a9`.
2. Run in **counting** mode over a real workload to enumerate the true call
   sites that trip it. — **DONE**, see "Stage 2": 1,427 violations in 39 spec
   files over the full 18,704-spec suite.
3. Fix those sites, **then** flip the default to a hard error. — **OPEN.**

Step 2 was the gate and it held: the static bound (7,218) overstates the runtime
blast radius by more than two orders of magnitude in file terms, and the
measurement is what makes step 3 finite. The eventual default must still be the
error — not a permanently-warning check.

## Stage 1 — counting mode (LANDED `2ca6b4da3a9`)

Seven slice implementations across four runtimes report the range they are about
to return to one audit; each engine's own existing UTF-8 validator decides
whether the slice turned valid UTF-8 into invalid UTF-8. Gate
`SIMPLE_UTF8_SLICE_AUDIT`, **default OFF** (`1` = count + log first per site,
`2` = count + log every occurrence). Nothing fails; no observable behaviour
changes.

## Stage 2 — measured blast radius (PROVED, 2026-08-01)

Measured with a purpose-built seed binary at base `f7b68068a3e` (`cargo build
--release --bin simple` in an isolated worktree; **no deployed binary carries
the audit** — `strings bin/simple` and
`bin/release/x86_64-unknown-linux-gnu/simple` both match
`SIMPLE_UTF8_SLICE_AUDIT` **0** times, so no measurement predating this build
can be real).

### The check is LIVE, not inert (PROVED)

A zero from a check that never ran is indistinguishable from a real zero, so
every enabled process emits one synthetic `site=self_test` violation, and the
probe carries aligned controls:

| run | stdout lengths | audit lines |
|---|---|---|
| `s[0:2]`, default engine | `bad=2 ok1=1 ok2=3 ok3=6` | `self_test`, **`rt_slice_rust start=0 end=2`** |
| `s[0:2]`, `SIMPLE_EXECUTION_MODE=interpret` | same | `self_test`, **`interp_bracket start=0 end=2`** |
| `.slice(0,2)`/`.substring(0,8)`, default | `a=2 b=8` | `self_test`, 2 × `rt_slice_rust` |
| `.slice(0,2)`/`.substring(0,8)`, interpret | `a=4 b=9` | `self_test`, 2 × `interp_method` |
| any of the above, gate unset **or** `=0` | unchanged | **0 lines** |

Three independent non-vacuity facts, all PROVED:
1. The **site name changes with the engine** (`rt_slice_rust` ↔ `interp_bracket`
   / `interp_method`) — the per-engine true-positive control, proving the two
   runs really used different engines and that each engine's own hook fired.
2. The **aligned controls `[0:1]`, `[0:3]`, `[0:6]` produce no lines** — the
   audit is not simply counting every slice.
3. The interpreter's lossy divergence reproduces exactly (`a_len` 4 vs 2,
   `b_len` 9 vs 8), matching the original byte-level evidence above.

### The census

Workload: **all 18,704 `*_spec.spl` under `test/`**, executed one process each
(`simple run <spec>`, default engine, `SIMPLE_UTF8_SLICE_AUDIT=2`, 25 s cap,
20-way parallel).

| quantity | value |
|---|---|
| spec programs executed | 18,704 |
| processes that reached the audit (`self_test` fired) | **2,051** (11.0 %) |
| **real violations** | **1,427** |
| — `interp_method` (`.slice`/`.substring`) | 833 |
| — `interp_bracket` (`s[a:b]`) | 594 |
| — `rt_slice_rust` (Cranelift JIT) | **0** — see caveat |
| distinct spec files that violate | **39** of 18,704 (0.21 %) |
| exit codes | 12,524 × 0 · 5,500 × 1 · 675 × timeout · 3 × SIGSEGV · 2 × 70 |

So the earlier "~7,218 candidate sites" is confirmed to be a **static** upper
bound: at runtime the defect concentrates in **39 spec files**, i.e. a small
number of production modules — which is exactly why staging mattered. Flipping
straight to a hard error would have failed those 39 immediately, and the count
was not knowable without measuring.

**Caveat — the `rt_slice_rust` zero is a COVERAGE GAP, not a live zero.** The
probe above proves that site fires under the default engine, so the hook is not
inert; but in-process specs fall back to the interpreter, so the spec suite
cannot exercise the JIT slice path at all. Do not read 0 as "the JIT is clean".

**Caveat — 5,500 specs exited 1 and 675 timed out at 25 s.** Those are
pre-existing at this base (the audit is default-off and read-only), but their
slices are unmeasured, so 1,427 is a **floor**.

**Not measurable here (PROVED, not assumed):** driving the pure-Simple compiler
(`simple run src/app/cli/main.spl …`, the command the bootstrap uses) produces
empty stdout, rc 0 and **zero audit lines including no `self_test`** under this
seed — the Simple `main` never executes, so the compiler-self-build workload
contributes nothing. The C sites (`rt_slice_c`, `spl_str_slice`,
`spl_str_slice_legacy`, `rt_slice_simple`) are likewise unexercised: standalone
`--native` still fails closed with `[CollectionOps]` on any function containing
a slice.

### Where the 1,427 come from

Grouped by subsystem (violations, spec files):

| subsystem | violations |
|---|---|
| `app/office/sheets` formula/locale text | 456 |
| browser engine + web browser session/renderer | 293 |
| JSON `\uXXXX` unescape (3 separate impls: `lib/common/json`, `lib/js`, `lib/common/js`) | 177 |
| editor md wiki index + md renderer | 132 |
| `torch` device-placement / training-seed status | 98 |
| `app/devhub` convert storage (multibyte) | 86 |
| HTML tokenizer / tree builder | 58 |
| TOML encoding (multibyte) | 42 |
| gdb-mi parser, glob, disk-image builder, `app/fix`, llm-cli, compiler lexer, misc | 79 |
| `bugs/text_slice_substring_spec` (the deliberate reproduction) | 6 |

The dominant shape is a **byte loop written as a character loop** — e.g.
`src/app/office/sheets/formula.spl:202,243,255,274,682,1529,…` all do
`val c = expr[i:i + 1]` while stepping `i` by 1. On ASCII input this is
harmless, which is why it survived; on any non-ASCII input every step past a
lead byte stores invalid UTF-8. The fix is to iterate by CHARACTER, which is
also the direction of the 2026-07-30 character-alignment decision.

### What the 1,427 actually ARE — this changes the stage-4 plan

Classifying every violation by slice width (PROVED, from the census log):

| width `end - start` | count | share | shape |
|---|---|---|---|
| **1 byte** | **1,254** | 87.9 % | `s[i:i + 1]` stepping `i` by 1 — a **scanner** |
| 2–3 bytes | 40 | 2.8 % | short fixed windows |
| >3 bytes | 133 | 9.3 % | wider windows |

The wide ones are mostly **not** truncation either: the torch-status cluster (98)
is a naive substring search taking a constant-width window at *consecutive*
start offsets (`start=97,98,99 … outlen=46` over an 8,855-byte document). So the
overwhelmingly dominant shape across all widths is a **byte-stepping scanner
that compares a fixed-width byte window against an ASCII literal** — code that
is *correct in aggregate* (it reassembles contiguous ranges) but that
materialises an invalid-UTF-8 value at every intermediate step.

**Consequence: erroring at the slice primitive would break essentially every
text scanner in the repo**, not a handful of buggy call sites. Stage 3 therefore
cannot be "fix 39 files"; it needs a **byte-oriented accessor** (or char-unit
iteration) for the scanner shape *first*, and only then can stage 4 flip. This
is the concrete blocker the measurement was run to find, and it was not visible
from the static 7,218-site count.

### Stage 3 prerequisite: the byte accessor ALREADY EXISTS — `byte_at` (2026-08-02)

The "byte-oriented accessor" this section asks for **was already in the tree**
when the section was written. `text.byte_at(i)` is landed and wired end to end;
no new primitive was needed. Verified present (PROVED, symbol + runtime):

| layer | site |
|---|---|
| C runtime | `src/runtime/runtime_native.c:2372` `rt_string_byte_at` (+ `__simple_` alias) |
| Simple runtime | `src/runtime/simple_core/core_string.spl:351` |
| Rust runtime (JIT/native) | `src/compiler_rust/runtime/src/value/collections.rs:2993` |
| Rust interpreter method | `src/compiler_rust/compiler/src/interpreter_method/string.rs` `"byte_at"` arm |
| Simple interpreter | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:101` |
| Simple MIR lowering | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2443` |
| Rust MIR lowering | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:1343` |
| LLVM + Cranelift codegen | `codegen/llvm/functions.rs:2404,2848`, `codegen/instr/calls.rs:3242` |

**Design, and why it is right (not a parallel vocabulary):**

- **Shape** — a method `s.byte_at(i)`, deliberately mirroring the existing
  `s.char_code_at(i)`. The pair is the whole point: `char_code_at` is
  CHARACTER-indexed, `byte_at` is BYTE-indexed, and `len()` is BYTE length
  (`rt_string_len`, "length of a string in bytes"). So `while i < s.len():
  s.byte_at(i)` is index-consistent, and the mixed-units hazard that produced
  the `strip_utf8_bom` bug is not expressible.
- **Returns a raw `i64`, NOT an Option** — and that is forced, not a shortcut.
  The nil sentinel IS the integer 3, so an INT-slot return cannot encode
  absence: an absent value would be indistinguishable from a real byte 0x03.
  (`substr` needed arity-aware dispatch to two symbols for exactly this.)
  Out-of-range therefore yields **0**, matching `char_code_at`'s convention.
- **Residual ambiguity, documented not hidden:** 0 is also a legal byte (NUL),
  so `byte_at` alone cannot distinguish "NUL" from "out of range". Callers must
  bound with `i < s.len()`. This is the price of the nil-sentinel constraint;
  it is not a defect, but it is a real sharp edge.
- **Not added to the two legacy C runtimes, deliberately.** `spl_str_slice` is
  duplicated in `runtime.c:328` and `runtime_legacy_core.c:182`, and neither
  has a byte accessor. Adding one would be a **defect, not a fix**: the bundle
  links with `-z muldefs` (`pipeline/native_project/linker.rs:1224,2240,2248`;
  see `scripts/check/check-runtime-bundle-duplicate-symbols.shs`, which records
  20 already-duplicated symbols), so a second `rt_string_byte_at` would be
  silently resolved first-definition-wins and drift into a wrong answer. One
  definition in `runtime_native.c`, shared through the bundle, is correct.

**Correctness PROVED against hand-computed expectations**, not cross-engine
agreement. For `s = "aé€𝄞z"` (`61 C3A9 E282AC F09D849E 7A`, 11 bytes) all 11
byte values, `len() == 11`, and the discriminator `byte_at(1) == 195` vs
`char_code_at(1) == 233` were checked on the Cranelift JIT (default engine) and
under `SIMPLE_EXECUTION_MODE=interpret`. `--native` remains UNMEASURABLE here
(fails closed with `[CollectionOps]`), so there is no native column.

### Defect found by that probe: negative index silently returned real data (FIXED)

The probe caught a live engine divergence that the accessor's own users would
have inherited. `"abc".byte_at(-1)` returned **0** on the JIT (the C impl guards
`if (index < 0) return 0;`) but **97** — a real byte — under the interpreter;
`char_code_at(-1)` likewise returned 97, and on `"ébc"` the two returned 195 and
233. Root cause: the interpreter arms read the index through `eval_arg_usize`,
which **saturates negatives to 0**. That saturation is correct for the
count/width callers it was written for (it fixed a `pad_left(-5)` capacity
panic) but wrong for an index accessor, where it converts an out-of-range index
into plausible data — a silent wrong answer.

Fixed in `interpreter_method/string.rs` by reading the index as a signed int and
returning 0 for negatives, matching the native impl and the sibling `char_at`
arm, which already guarded this way. RED before GREEN on both arms and both the
ASCII fast path and the non-ASCII walk; positive controls (`byte_at(0) == 97`,
out-of-range `byte_at(3) == 0`) held throughout, so the green is not vacuous.

A genuine-bug class does exist inside the remainder, and counting mode found it:

- **`strip_utf8_bom` — FIXED in this change.** `src/lib/common/encoding/text_ops.spl:112`
  tested the BOM with `char_code_at(0)` (**character**-indexed, returns 65279)
  and then stripped it with `s.slice(1, s.len())` (**byte**-indexed). U+FEFF is
  3 bytes, so it dropped only the lead byte and returned the two orphaned
  continuation bytes as the head of the result — invalid UTF-8, and 2 bytes
  longer than asked for. Audit line: `start=1 end=14 srclen=14 outlen=13`.
  Direct probe before: `out_len=13, equal=false`; after: `out_len=11,
  equal=true`, byte-identical on the default engine and under
  `SIMPLE_EXECUTION_MODE=interpret`, with the violation line gone and the
  `self_test` liveness control still firing (so the zero is measured, not
  inert). `test/01_unit/lib/common/encoding/text_ops_bom_spec.spl` exited **1**
  in the census and now passes **3 examples, 0 failures**.

This is the mixed-units hazard the 2026-07-30 character-alignment decision is
meant to remove: one function used a character index and a byte index on the
same string. Other single-occurrence wide-span sites (e.g. a `[0:14]` truncation
of a 33-byte string in `ui/window` scene-render) are likely the same shape and
remain OPEN.

### Stage 3 migration — batch 1: `lib/common/json/parser.spl` (2026-08-02)

First scanner migrated onto `byte_at`. The three pure-classification scanners
(`json_skip_whitespace`, `json_string_escapes_are_valid`, `json_number_is_valid`)
now read `s.byte_at(i)` and compare against byte constants (`44`, `48`..`57`,
`92`, …) instead of slicing a 1-byte window and comparing it to an ASCII
literal. Because the comparison is integer, **no text value is materialised at
all**, so the invalid-UTF-8 intermediate cannot exist — this is a removal of the
defect, not a relabelling of it.

Measured with the audit as the instrument, same spec, same binary, on **both**
reachable engines. The audit's `site=` field changes with the engine, so these
are two genuinely different slice implementations, not one measured twice:

| engine | audit site | before | after | liveness |
|---|---|---|---|---|
| Cranelift JIT (default) | `rt_slice_rust` | **18** | **0** | `self_test` present |
| `SIMPLE_EXECUTION_MODE=interpret` | `interp_bracket` | **18** | **0** | `self_test` present |

(`--native` remains UNMEASURABLE — it fails closed with `[CollectionOps]` — so
there is no native column.)

Behaviour is unchanged: the 17 assertions (valid/invalid numbers, escape forms,
`\uXXXX`, and non-ASCII `é`/`€`/`𝄞` inputs) produce a byte-identical `diff`
across the two versions, and `json_unicode_escape_spec.spl` (15 examples) and
`json_1_complete_spec.spl` (15 examples) both pass 0 failures.

**Measurement trap recorded, because it nearly produced a false green.** The
audit's `self_test` liveness line is emitted lazily, on the FIRST slice
operation in the process (`text_slice_audit.rs::level()`). A migration that
removes *every* slice from a path therefore also removes the liveness line, so a
genuine 0 is initially indistinguishable from a run that never reached the
audit — the first AFTER run reported exactly that and was correctly rejected as
INERT. The driver now performs one deliberately **codepoint-aligned** slice
(`"aé"[0:1]`, cutting exactly on the `a`/`é` boundary) which initialises the
audit and contributes no violation, so the 0 above is measured, not inert.

Remaining in this file: 5 sites in the tokenizer, which **accumulate** the
1-byte slice into an output string rather than only classifying it. That shape
cannot be converted by a byte compare; it needs run-slicing at codepoint
boundaries and is a larger refactor. It is OPEN.

Two further facts this migration settles:

- The in-file comments admitted the old idiom's index space was **chars under
  the interpreter, bytes under compiled code, while `len()` is bytes** — an
  engine divergence living inside the parser. `byte_at` is byte-indexed on every
  engine, so the migration removes that divergence as well.
- The empty-slice "logical EOF" sentinel the old loop relied on is gone; the
  `i < s.len()` bound already covers it, and a real NUL byte is now correctly
  rejected as an unescaped control character rather than silently ending the scan.

### Why the flip to a hard error is DEFERRED

1,427 live violations across 39 spec files is not a justified residual, and
87.9 % of them are the scanner idiom rather than buggy call sites. Making the
check loud now would not surface 39 bugs; it would break every byte-stepping
text scanner in the repo, plus whatever the two unmeasured surfaces (JIT,
native/C) contribute. Stage 3 must land first. The eventual default must still
be the **error** — not a permanently-warning check.

**Status 2026-08-02 — still DEFERRED, but the blocker changed shape.** The
prerequisite this section named (a byte-oriented accessor) is **met**: `byte_at`
already existed, is wired on every engine, and is now proved correct against
hand-computed values. What remains is not design work but migration volume.

Honest accounting of the 1,427:

- **18 removed** and PROVED to 0 (`lib/common/json/parser.spl`, batch 1 above).
- **~1,409 remain.** This lane migrated one file; it did not re-run the
  18,704-spec census, so the repo-wide total is *not* re-measured. Treating
  "1,427 − 18" as the new census figure would be INFERRED, not measured, and the
  subsystem attributions in the table above are per-spec-file, not per-source-file.
- Static sweep of the scanner idiom `X[i:i + 1]` across `src/` finds **901
  sites** (PROVED, `grep`), of which 10 are now migrated, leaving **891**. That
  count is the realistic size of stage 3, and it is the number to plan against —
  not 39 files. Classified by how the sliced value is consumed (PROVED, `grep`):

  | shape | sites | migration cost |
  |---|---|---|
  | compared directly against a literal on the same line | 239 | mechanical — becomes an integer compare, batch-1 shape |
  | bound to a `val`/`var` first | 461 | depends on downstream use: classification converts, accumulation does not |
  | other (argument position, nested expression) | 191 | inspect individually |

  Top concentrations: `browser_engine` layout renderer (36), `fix` lint rules
  (29), editor LSP/DAP/diagnostics panels (~100 across a dozen files), the three
  duplicated `gdb_mi_parser` copies (30), `office/sheets` (~30).

The migration is mechanical but **not** blind-automatable: each site must be
classified first. Sites that only *classify* the byte convert cleanly to an
integer compare (batch 1's shape). Sites that *accumulate* the 1-byte slice into
an output string do not, and need run-slicing at codepoint boundaries. A
regex-driven bulk rewrite would silently convert the second class wrongly, so
batches must stay small and each must carry a before/after audit measurement
with the liveness control described above.

Recommendation: **do not flip yet.** The remainder is dominated by the scanner
idiom, not by genuine bugs, so a flip today would still break working scanners.
Revisit the flip once the 901 sites are down to a residual small enough to
inspect by hand; at that point the remainder should be genuine defects of the
`strip_utf8_bom` class and the error becomes the right default.

Reproduce the census:

```
SIMPLE_UTF8_SLICE_AUDIT=2 <seed-with-audit> run <spec> 2>&1 |
  grep '^SIMPLE_UTF8_SLICE_AUDIT '
```

Subtract exactly one `site=self_test` line per process. A run with **no**
`self_test` line did not reach the audit and its zero is inert.

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

## Fence added 2026-08-08 — `check-native-utf8-slice.shs`

Added `scripts/check/check-native-utf8-slice.shs` and fixture
`test/fixtures/native_utf8_slice/main.spl` (probe string `s = "aé€𝄞z"`,
identical to the "Reproduce" section above). This closes the false-green gap
named in `doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md`
row 5.

**What the pre-existing partial fence (`check-utf8-slice-audit-live.shs`)
covers and what it misses, confirmed by reading it:** it only proves the
`SIMPLE_UTF8_SLICE_AUDIT` counting instrument is compiled into the checked
binary (a `strings` grep) and that its `self_test` liveness line fires under
plain `run`. It never drives `native-build` or `compile --native`, and it
never inspects the LEN or bytes of any slice result — so a suite pointing at
it would believe the native lane's *slicing policy* is covered when only a
diagnostic *counter* is. That is the false-green gap this session closed.

**New fence, `check-native-utf8-slice.shs`, pins six things, all verified
today (2026-08-08) against the live binary at `bin/simple`:**

1. Aligned control `s[0:3]` (cuts on a codepoint boundary): `len=3` on both
   the default (Cranelift JIT) engine and `SIMPLE_EXECUTION_MODE=interpret`.
   Hard-asserted (not KNOWN-OPEN) — this is the true-positive control.
2. `s[0:2]` (bracket slice, splits `é`): **KNOWN-OPEN** — both engines return
   raw, unvalidated bytes, `len=2`. Correct-should-be: a hard error, per this
   doc's "Semantics decision" section.
3. `.slice(0,2)`: **KNOWN-OPEN** — interpreter returns lossy-U+FFFD (`len=4`),
   JIT returns raw bytes (`len=2`). The two engines disagree with each other
   *and* with policy 2's bracket-slice raw-bytes value.
4. `.substring(0,2)`: same divergence as `.slice`, **KNOWN-OPEN**.
5. `simple compile <fixture> --native`: **KNOWN-OPEN**, still fails closed
   with the exact diagnostic
   `cannot compile to standalone native binary: 1 function(s) contain
   constructs that require the interpreter: - main: [CollectionOps]` — this
   reproduces the bug doc's "Engine-reachability caveat" verbatim, so the
   native raw-bytes policy remains unreachable through this command.
6. `simple native-build --source ... --entry-closure --entry <fixture>`:
   **a new, previously-undocumented finding.** This command does NOT give the
   same clean diagnostic as (5). It also fails (rc≠0, so no wrong binary is
   ever produced) but with an opaque, unrelated-looking internal error:
   `error: semantic: undefined field 'kind': cannot access field on value of
   type 'nil'`, raised inside MIR lowering right after
   `[mir-lower-expr] method-dispatch-before method=slice` /
   `[mir-method-call] start method=slice argc=2` — i.e. triggered by the
   bracket-slice-to-`.slice()` desugar, not by any UTF-8-specific code.
   Reproduced on a minimal 3-line ASCII-only control (`s[0:2]` on `"abc"`,
   isolated in its own source directory) — so this is a general
   `native-build`-vs-`.slice()` defect, not specific to multi-byte input or to
   this fixture. A no-slice control (`print(s)`, same shape) compiles and runs
   correctly under `native-build`, isolating the trigger to the slice call.
   Recorded as **KNOWN-OPEN**, distinct from (5), because a fix to either path
   is independently visible: `native-build` could start emitting the same
   clean `[CollectionOps]` diagnostic (still closed, wording unified) or could
   start compiling (gap fully closed) — the script's three-way branch reports
   either outcome as a `NOTE` rather than a silent pass.

**Sabotage-verified (2026-08-08, both directions performed and confirmed):**
mutated the fixture's aligned-control line from `s[0:3]` to `s[0:2]`, re-ran
the script — result `FAIL — aligned control s[0:3] regressed (expected len=3
on both engines) / JIT len=2  interpret len=2`, exit 1. Restored the line to
`s[0:3]`, re-ran — full `PASS` on all six checks, exit 0, and the file's
content was diffed back to the original 18-line fixture to confirm no residual
mutation. The assertion is load-bearing, not vacuous.

**Explicit scope statement — what this fence does NOT establish:** `--native`
and `native-build` both remain UNREACHABLE for the raw-bytes native slicing
policy itself (rows 5–6 above only pin the *refusal*, not a slice value
produced by either native path) — exactly as the bug doc's "Engine-reachability
caveat" already stated; this session did not change that. The fence also
covers only the Cranelift JIT and the interpreter for the three slicing
policies (rows 1–4); LLVM-without-`--native` and the C runtime's
`spl_str_slice`/`spl_str_slice_legacy` legacy duplicates remain unmeasured, as
they were before. No fix was attempted for the underlying divergence or for
the `native-build` opaque-error defect — per the task's explicit scope, the
891-site migration decision from "Stage 3 migration" above stands unchanged.

## Re-verified 2026-08-09 — row 6's premise FALSIFIED; native-build now REACHES the raw-bytes policy (still open, not fixed)

The fence's B2 branch (`native-build`) flagged its own `FAIL (promote-me)`
convention: `nb_rc=0` where the pinned premise said it should stay nonzero.
Re-ran the underlying repro directly (not just the fence) to characterize the
drift before touching anything:

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
    --source <dir with fixture> --entry-closure --entry <fixture>/main.spl \
    --cache-dir <cache> --output <bin>
```

Build now succeeds (rc=0, 32112-byte standalone binary, no interpreter present
at runtime). Running the produced binary and inspecting stdout byte-for-byte
(`od -c` / `xxd`):

| tag | len | bytes |
|---|---|---|
| `bracket_ctl` (`s[0:3]`, control) | 3 | `61 c3 a9` — correct, both codepoint bytes |
| `bracket_cut` (`s[0:2]`, splits é) | 2 | `61 c3` — **truncated mid-codepoint, invalid UTF-8** |
| `slice_cut` (`.slice(0,2)`) | 2 | `61 c3` — same truncation |
| `substring_cut` (`.substring(0,2)`) | 2 | `61 c3` — same truncation |

This is byte-identical to the raw-bytes policy already pinned above for the
Cranelift JIT (rows 1–3): a mid-codepoint slice silently produces 2 raw bytes
with no UTF-8 validation and no error. **Verdict: NOT fixed.** What changed is
reachability — the whole-program `native-build` AOT path used to fail closed
(opaque `undefined field 'kind'` MIR-lowering error) on any function
containing a slice; it now silently compiles the slice and materializes the
invalid-UTF-8 value into a real standalone executable with no interpreter
present. That is a narrowing of "this defect is unreachable through native
tooling," not a repair — if anything it slightly *widens* the defect's
observable blast radius (a shippable native artifact can now carry it),
though it does not change which policy is applied.

Root cause of the reachability change not investigated (out of scope for this
pass — no fix was attempted, per this doc's standing scope statement above).

Separately observed, not examined further: the native-build binary's `print()`
emits **no newlines** between successive calls at all (all four `dump()` lines
land back-to-back in one unbroken byte run) — a distinct divergence from
`bin/simple run`'s output, unrelated to the UTF-8 slicing policy itself.

`scripts/check/check-native-utf8-slice.shs` B2 was re-pinned accordingly: it
no longer reports `FAIL (promote-me)` on `nb_rc=0`; it now runs the produced
binary and hard-asserts the exact byte-level raw-bytes-truncation shape above,
reporting `KNOWN-OPEN` when it matches (current state) and `FAIL`/`NOTE` if it
ever drifts (aligned-control regression fails hard; any other shape change is
flagged for human re-triage rather than silently re-accepted). Sabotage-verified
2026-08-09: mutating the fixture's control line to `s[0:2]` reproduced the
fence's `FAIL — aligned control s[0:3] regressed` on both the existing Part-A
assertion and the new native-build byte-level assertion; restoring the line
returned a clean `PASS` on all branches.


## Resolution (2026-08-21) — the interpreter was the wrong engine

Measured at `origin/main` `f5823c5ab74`, seed built from a clean worktree
(sha256 `53af156a5bbac8db`). The differential fixture
`test/fixtures/engine_differential/utf8_slice_boundary.spl` reproduced the split
exactly as documented above: `slice_len` and `substring_len` were **4** on
interpret and **2** on jit, while `bracket_split_len` was 2 on both.

### Which engine was right, and why

Byte-indexed slicing is the DESIGN, not an accident, and it was already decided
and implemented for the bracket path. `interpreter/expr/collections.rs`
(`Expr::Slice`, `Value::Str` arm) returns `Value::text_from_bytes(...)` with a
comment recording why: U+FFFD substitution there "shredded every 1-unit slice
walk (json/toml tokenizers) because the original byte was unrecoverable at
concat time". `Value::StrBytes` exists precisely to carry a mid-codepoint
fragment until concatenation re-validates it, and `len`/`index_of` are
byte-valued so their results are valid inputs to `slice`.

The `.slice`/`.substring` METHOD arm in
`compiler/src/interpreter_method/string.rs` was simply never migrated to that
decision. It computed the correct byte range and then ran it through
`String::from_utf8_lossy`, which is valid-but-wrong: it CHANGES the byte length
of the result (a 2-byte range came back with `len() == 4`) and destroys the
original byte. The interpreter was the outlier against its own bracket path AND
against both compiled lanes, so it is the engine that was fixed. The JIT/native
`rt_slice` was not touched.

One line changed:

```rust
-let result = String::from_utf8_lossy(&bytes[start..end]).into_owned();
-return Ok(Value::text(result));
+return Ok(Value::text_from_bytes(bytes[start..end].to_vec()));
```

`text_from_bytes` collapses back to a normal `Str` whenever the bytes are valid
UTF-8, so aligned slices — the overwhelming majority — are bit-identical to
before.

### Evidence

| expression | interpret before | interpret after | jit (unchanged) |
|---|---|---|---|
| `s[0:2].len()` | 2 | 2 | 2 |
| `s.slice(0, 2).len()` | **4** | **2** | 2 |
| `s.substring(0, 2).len()` | **4** | **2** | 2 |
| `s.slice(0, 8).len()` | **9** | **8** | 8 |
| `s.slice(0,2) + s.slice(2,11)` | corrupted | `aé€𝄞z` | `aé€𝄞z` |

The fixture was extended with the wide-split, empty (`slice(3,3)`), overrun
(`slice(6,99)`) and reassembly cases, and **removed from the harness's
`baselines()`** — that list is now empty, which is its correct state. Full
corpus, `DIFF_LANES=interpret,jit`: `PASS — 13 fixture(s) compared across 2
lane(s), 0 new divergences (0 baselined, 0 lane error(s))`.

Tests: new `compiler/tests/interpreter_utf8_slice_boundary.rs`, 5/5 — split
ranges keep their byte width, the three spellings agree, adjacent split slices
reassemble the original, aligned ranges are unchanged (the non-vacuity
control), and empty/overrun ranges clamp. Every assertion is on an integer
length or a reassembled string, never on a printed glyph, because `print()`
renders the lossy and the raw forms identically.

`test/01_unit/bugs/text_slice_substring_spec.spl` §"Test Group 8" pinned the OLD
lossy behaviour as intentional (`expect(bad).to_equal("\u{FFFD}")`). Its
`codepoint-boundary safety` context was rewritten to pin the raw-byte invariant
instead: the length of a byte slice equals the width of its range, and adjacent
slices reassemble. The spec was not deleted, and its docstring records what
changed and why.

### Not changed

- Stage 4 (mid-codepoint slice as a hard error) is still deferred, for the
  reason already recorded: the byte-stepping call sites measured in Stage 2.
  Unifying the engines does not make that flip any safer.
- The native lane could not be measured — `native-build` fails at this tip for
  an unrelated pre-existing reason (`method \`replace\` not found on type
  \`function\``, function `hash_text`), so it reports LANE_ERROR before any
  fixture runs. `rt_slice` itself was not modified.
