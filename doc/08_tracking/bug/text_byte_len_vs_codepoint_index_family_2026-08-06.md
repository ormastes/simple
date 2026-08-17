# Byte-length vs codepoint-index confusion in text handling (family sweep)

- **Date:** 2026-08-06
- **Scope swept:** `src/lib/**` (7,542 `.spl` files, vendor excluded)
- **Status:** 2 sites fixed and landed; 2 systemic root causes filed below (both
  live outside `src/lib`, so they are recorded rather than patched here)

## Measured primitive table

Measured directly, not assumed. Probe strings `"abc"` and `"aé€😀z"`
(5 codepoints, 11 bytes). Both engines driven through `bin/simple run`, which
currently reports `WARNING: this Rust-built Simple binary is a bootstrap seed
only` — so these are **seed-JIT** and **seed-interpret** columns, not a
bootstrapped self-hosted binary.

| expression | seed-JIT | seed-interpret | unit |
|---|---|---|---|
| `"aé€😀z".len()` | 11 | 11 | **BYTES** |
| `"aé€😀z".length()` | 11 | 11 | **BYTES** (exact alias of `len()`) |
| `"aé€😀z".bytes().len()` | 11 | 11 | BYTES |
| `char_at(i)` valid range | 0..4 | 0..4 | **CODEPOINTS** |
| `char_at(overrun)` | `nil` | `""` | **DIVERGES** |
| `char_at(overrun) as i64` | `0` (silent) | abort: `cannot cast str to i64` | **DIVERGES** |
| `"Café".char_at(3) as i64` | **394395739456** | `233` | **JIT RETURNS A POINTER** |
| `char_code_at(i)` | correct (233) | correct (233) | CODEPOINTS |
| `char_code_at(overrun)` | `0` silently | `0` silently | silent |
| `"aé€😀z"[1:2]` | U+FFFD | U+FFFD | **BYTES, splits UTF-8** |
| `(97).chr()` | **`Function 'i64.chr' not found`** | `"a"` | **JIT MISSING** |

Three consequences that drive every verdict below:

1. `len()` and `length()` are the same byte count. A loop bounded by either and
   indexed with `char_at`/`char_code_at` over-runs on any non-ASCII input.
2. The common defensive idiom `if ch == "": break` **does not work on JIT**,
   where the overrun value is `nil`, not `""`. It is fail-open exactly where the
   overrun happens.
3. `s[i:i+1]` is byte slicing on **both** engines. The note at
   `src/lib/common/json/parser.spl:82-84` claiming it slices chars under the
   interpreter did not reproduce and should be re-checked.

## Enumeration

Anchored scan (`/usr/bin/grep` pinned; ugrep is the default `grep` here), loop
bound resolved back through intervening `val`/`var` bindings, subject required
to be text-typed:

| class | shape | sites |
|---|---|---|
| 0 | all `.len()`/`.length()`-bounded loops in `src/lib` | 6,247 |
| — | …narrowed to text-shaped subjects | 762 |
| 1 | `char_at`/`char_code_at(i)` bounded by a BYTE `len()` | **332** |
| 1a | …where the value is then cast to an int (the abort signature) | **12** |
| 2 | `s[i:i+1]` bounded by a BYTE `len()` | see scan |
| 3 | `.chr()` call sites (interpreter-only builtin) | **100** |

Class 1a, the exact signature of the two already-confirmed instances:

```
src/lib/common/ui/theme_package_wire.spl:121,149   value.char_at(i) as i64
src/lib/common/ui/html_ui/doc_ops.spl:176          s.char_at(i) as i64
src/lib/common/base_encoding/base32.spl:125        encoded.char_at(i) as i64   [FIXED]
src/lib/common/base_encoding/base64.spl:97         encoded.char_at(i) as i64   [FIXED]
src/lib/common/image/ppm_decode.spl:137            header.char_at(hi) as i64
src/lib/nogc_async_mut/fs_driver/fat32_dir_ops.spl:75,93,177,195,430,448
                                                   name.char_at(di) as u8
```

Class 1a is **not** the whole family — it is only the subset that aborts. The
`char_code_at` sites (e.g. `nogc_sync_mut/aws_sigv4.spl:29,66`,
`oauth2.spl:221`, `udp_utils.spl:348`, `common/cert/x509_typed.spl:472`,
`config_core/schema.spl:204,216,235`) return `0` on overrun on both engines and
so corrupt silently instead. They are the same defect with a quieter failure.

## Root causes (outside `src/lib`) — BOTH FIXED 2026-08-06

Both were seed **Cranelift** (default `run`) gaps; the tree-walk interpreter,
the LLVM backend and the pure-Simple compiler all already did the right thing.
Evidence binary: `src/compiler_rust/target/bootstrap/simple` (the seed), run
directly. Fixes:

| root cause | fix site | mechanism |
|---|---|---|
| R1 (cast) | `runtime/src/value/sffi/value_ops.rs` `rt_value_as_int` | `char_at` has no `method_return_types` entry so it falls through to `TypeId::ANY` (`hir/lower/expr/mod.rs:920`); `compile_cast`'s ANY→int arm (`codegen/instr/basic_ops.rs:54`) calls `rt_value_as_int`, which was an unconditional `(self.0 as i64) >> 3` — the heap pointer for a text value. Now decodes text: a single codepoint yields that codepoint (the interpreter's documented contract), longer text falls back to the leading-digit-run parse the STRING-typed arm already uses. |
| R2 (`chr`) | `compiler/src/codegen/instr/calls.rs` qualified-method table | no `chr`/`to_char` arm, so the call fell through to a cross-module import and died as `Function 'i64.chr' not found`. Routed to `text_dot_from_char_code`, the same runtime entry point the LLVM backend already calls. |
| R2b (fail-open) | `runtime/src/value/collections.rs` `rt_string_char_at` | forward over-run returned `RuntimeValue::NIL` at **two** sites (byte-length fast reject and the real codepoint bound); both now return empty text, matching the interpreter, so `if ch == "": break` terminates. |

`.chr()` was kept, not removed: four independent implementations exist
(tree-walk interpreter `interpreter_method/primitives.rs:212`, pure-Simple
interpreter `10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:1056`,
LLVM ×3, pure-Simple MIR lowering
`50.mir/_MirLoweringExpr/method_calls_literals.spl:1005`). One missing dispatch
arm is not grounds for a 100-site migration.

**Residue, filed not fixed:** multi-character text cast to an integer still
diverges — the interpreter raises `cannot cast str to i64`, the compiled path
returns the lenient parse. `rt_value_as_int` returns a bare `i64` with no error
channel, so agreement there needs a wider ABI change.

Contract pinned in `test/01_unit/language/text_char_primitive_engine_contract_spec.spl`
(interpreter-only by construction — `simple test` has no JIT mode; the JIT half
is proved by `<seed> run` with/without `SIMPLE_EXECUTION_MODE=interpret`).

### R1. `char_at(i) as i64` returns a raw pointer on JIT for non-ASCII

`"Café".char_at(3) as i64` yields `394395739456` on JIT and `233` on the
interpreter. This makes *every* `char_at(i) as i64` site wrong on the default
engine regardless of its loop bound, so the correct fix at these sites is to
iterate `s.bytes()` — not merely to correct the bound to a codepoint count.
Lives in the codegen/runtime cast path (`src/compiler/**` / `src/runtime/**`).

### R2. `i64.chr` is missing on JIT — 100 call sites in `src/lib`

`(97).chr()` aborts on JIT with `Function 'i64.chr' not found`. The replacement
`char_from_codepoint` (`src/lib/common/encoding/utf8.spl:341`) builds the
character from a literal table slice plus `rt_bytes_to_text` and works on both
engines. 100 sites in `src/lib` still call `.chr()`, including
`common/json/parser.spl:399-413`, `common/js/builtins/json.spl:118-135`,
`common/ui/html_ui/payload.spl:155-186`, `common/ui/html_ui/doc_ops.spl:179`,
`common/aes/utilities.spl:135`, `nogc_sync_mut/sfm/codec.spl:143-161`,
`nogc_sync_mut/js/engine/*`. Each is a JIT-path outage in whatever public API
reaches it. Either restore `i64.chr` in codegen or sweep the 100 sites.

## Fixed and landed by this sweep

| commit | site | symptom before |
|---|---|---|
| `5b41ee6e580` | `base_encoding.spl` `_char_from_code` | `bytes_to_text` aborted on JIT with `Function 'i64.chr' not found` — for ASCII input too, since the ASCII fast path shares the helper |
| `a7d5a01955d` | `base_encoding/base64.spl` | `base64_decode` returned `""` **silently** on JIT for all input, ASCII included (R1 via the `char_at` cast), and aborted via R2 once that was fixed |
| `9b392e37162` | `base_encoding/base32.spl` | `base32_decode` returned an empty `[u8]` **silently** on JIT for all input, ASCII included (R1) |

Both proved by public-API round trip with an ASCII control in the same run,
2/3/4-byte codepoints (`é`/`€`/`😀`), on both engines, with per-half sabotage.

## Engine caveat — read this before quoting any proof

Every measurement and every RED/GREEN/sabotage transcript in this sweep was
produced by `bin/simple run`, which currently prints `WARNING: this Rust-built
Simple binary is a bootstrap seed only`. So all evidence is **seed-JIT** and
**seed-interpret**. The bootstrapped self-hosted binary was *not* exercised —
a full bootstrap was out of scope for this sweep. The four fix commits
(`5b41ee6e580`, `a7d5a01955d`, `9b392e37162`) say "the default (JIT) engine";
read that as **seed-JIT**. The defects are in `src/lib` source and are engine
independent in origin, but the observed failure *modes* are seed-path
observations and should be re-confirmed on a self-hosted binary before anyone
claims the self-hosted path is fixed.

## Triage verdict for every remaining candidate

### Confirmed broken, NOT fixed (need their own change + proof)

| site | verdict |
|---|---|
| `nogc_sync_mut/aws_sigv4.spl:29` `_text_to_bytes` | **BROKEN.** `out.push(s.char_code_at(i))` bounded by `s.len()` (BYTES) pushes *codepoints* for valid indices and phantom `0`s for the over-run. Despite the name it does not produce bytes at all for non-ASCII. Any SigV4 payload hash over non-ASCII text is computed over the wrong sequence *and* NUL-padded, so the signature is wrong. Should iterate `s.bytes()`. |
| `nogc_sync_mut/aws_sigv4.spl:66` `sigv4_uri_encode` | **BROKEN, two units in one loop body.** `ch = s[i:i+1]` is a BYTE slice while `code = s.char_code_at(i)` is a CODEPOINT — the same iteration reads the string in two different units, bounded by a BYTE count. Percent-encoding is defined per byte, so non-ASCII URI components encode incorrectly. Takes arbitrary URI components, so plainly reachable. |
| `nogc_async_mut/fs_driver/fat32_dir_ops.spl:75,93,177,195,430,448` | **BROKEN, reachable.** 8.3 short-name generation, `name.char_at(di) as u8` bounded by `name.len()` (BYTES). Non-ASCII filenames are ordinary input and nothing upcases or filters before this loop; `as u8` on a JIT `char_at` result is also R1 garbage. One family, one fix, one proof. |
| `common/ui/html_ui/doc_ops.spl:176` `_to_lower` | **BROKEN, both root causes in one function.** R1 at :177 (`s.char_at(i) as i64` bounded by BYTE `len()`) *and* R2 at :179 (`(code + 32).chr()`), so on seed-JIT it fails for plain **ASCII uppercase** — no non-ASCII needed. Reached from :135/:137 on HTML tag-name fragments. |

### Ruled out, with reason

| site | verdict |
|---|---|
| `common/ui/theme_package_wire.spl:121,149` | **Right outcome, wrong mechanism — not fixed.** Both parsers reject anything outside `48..57` with `Err(...)`. On JIT the R1 pointer garbage lands outside that range, so a non-ASCII input still returns `Err("malformed")`. The contract holds by accident, not by construction. Fixing R1 would make it correct by construction; leaving it is not a live data defect. |
| `common/image/ppm_decode.spl:137` | **ASCII-by-contract.** The PPM header grammar (`P6\n<w> <h>\n255\n`) is ASCII by format specification, so byte count and codepoint count provably coincide on any well-formed header. |
| `common/config_core/schema.spl:204,216,235`, `common/cert/x509_typed.spl:472`, `crypto/x25519_mlkem768/*` (3), `nogc_sync_mut/oauth2.spl:221`, `udp_utils.spl:348` | **Same shape, over-run only.** `char_code_at` returns correct codepoints on *both* engines, so these fail only by the loop over-running and processing phantom `0` codepoints past the end. Benign where the trailing `0`s fail a validity test anyway (schema, x509, oauth2 scope charsets); **not** benign anywhere the result feeds a digest or canonical string, since trailing NULs change the hash. Flagged for the next lane rather than fixed here — none is on the base_encoding path this sweep was scoped to. |

### Class-2 (`s[i:i+1]`) — a documented note is wrong

`conf.spl:75`, `glob.spl:76`, `glob.spl:115`, `path.spl:227` bound `s[i:i+1]`
by a BYTE `len()`. Measurement says `s[i:i+1]` slices **BYTES on both
engines** — so these are self-consistent (byte bound + byte slice) and are
*not* defects, and they are also not the interpreter-vs-compiled divergence
that `src/lib/common/json/parser.spl:82-84` describes. That note did not
reproduce and should be corrected or deleted; a lane relying on it will draw
the wrong conclusion.

## Follow-up 2026-08-17 — primitive table RE-CONFIRMED; class-1a site at theme_package_wire hardened

### The class is still real

Re-measured on `bin/simple run` (seed binary) with the same probe string
`"aé€😀z"` (5 codepoints, 11 bytes):

| expression | measured 2026-08-17 |
|---|---|
| `"aé€😀z".len()` | 11 — **BYTES** |
| `"aé€😀z".length()` | 11 — **BYTES** |
| `"aé€😀z".char_at(4)` | `"z"` — **CODEPOINTS** (last cp at index 4) |
| `for ch in "aé€😀z"` iterations | 5 — **CODEPOINTS** |
| `char_at(overrun) == ""` | `true` (interpreter path) |

So the mismatch that defines this family is unchanged: `len()`/`length()` are
byte counts, `char_at`/`char_code_at` are codepoint-indexed, and `for ch in s`
is the codepoint-correct iteration form.

Two entries of the original table did NOT reproduce and should be re-measured
before being relied on: `(97).chr()` now works (`-> "a"`), and
`_theme_wire_parse_*` on multibyte input returned `Err` rather than aborting
with `cannot cast str to i64`.

### `theme_package_wire.spl:121,149` — hardened, but it never had an observable RED

Honest finding: the two sites are byte-bounded exactly as documented, but they
cannot be driven to a **wrong answer**. Both are digit *validators*: `char_at`
is codepoint-indexed, so any non-ASCII codepoint is reached and rejected
(`code < 48 or code > 57`) BEFORE the byte bound can over-run, and an overrun
value coerces to `0`, which also fails the digit test. Probed directly:
`_theme_wire_parse_u32("1é")` and `_theme_wire_parse_i32("-1é")` both return
`Err`. Correct by accident, not by construction.

Changed anyway, because "correct by accident" is one refactor away from wrong:
both loops now iterate codepoints (`for ch in value:` + `ch.char_code_at(0)`)
instead of `while i < value.len(): value.char_at(i) as i64`. No behaviour
change is expected or observed. `_theme_wire_parse_i32`'s `start` offset is
kept as a codepoint index — it is 0 or 1 and only ever skips an ASCII `-`.

Specs added:
- `test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl`
  (site: ASCII accept/reject contract + non-ASCII rejection, both parsers)
- `test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl`
  (class detection: pins the byte-vs-codepoint primitive contract and the
  shared codepoint-correct measurement leaf `common/layout/text_metrics.spl`
  that both this family and the live-lane inline-text bug route through)

### Re-checked and found clean

`src/lib/common/image/ppm_decode.spl:137` is listed as class 1a but is not
defective: its `header` is a locally built `"P6\n{width} {height}\n255\n"`,
always ASCII, so byte length and codepoint count coincide by construction.
