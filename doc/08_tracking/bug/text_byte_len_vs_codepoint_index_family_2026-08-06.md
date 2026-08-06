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
src/lib/common/base_encoding/base32.spl:125        encoded.char_at(i) as i64
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

## Root causes (outside `src/lib`, filed not fixed)

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

Both proved by public-API round trip with an ASCII control in the same run,
2/3/4-byte codepoints (`é`/`€`/`😀`), on both engines, with per-half sabotage.

## Not yet triaged

The remaining 10 class-1a sites and the `char_code_at` set still need the
reachability question answered per site: can non-ASCII actually reach this
argument? `fat32_dir_ops.spl` (6 sites, one 8.3 short-name family) is the most
likely to be genuinely reachable, since non-ASCII filenames are ordinary input.
