# CoreLexer: binary/octal literals lost their type suffix; radix digit runs capped at 64

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** compiler front end — `src/compiler/10.frontend/core/lexer_struct.spl`, `CoreLexer.scan_number`
- **Engines:** pure-Simple front end (CoreLexer is the only live tokenizer; the
  free-function scanner cluster was deleted 2026-07-29, see
  `lexer_position_unification_2026-07-29.md`).

## Defect 1 — `0b`/`0o` literals with a type suffix were split into two tokens

`scan_number` had a type-suffix scan in the hex branch (added for
`mixed_unsigned_float_comparison_llvm_2026-07-16`) and in the decimal branch,
but **not** in the `0b` and `0o` branches. Those branches stopped at the first
non-radix character, emitted a plain `TOK_INT_LIT` (kind 1), and never called
`core_token_suffix_save`. The alpha run then lexed as a **separate identifier
token**:

| source | before (kind:text) | after |
|---|---|---|
| `0b1010u64` | `1:0b1010` \| `6:u64` | `7:0b1010` suffix `u64` |
| `0b1010_u64` | `1:0b1010_` \| `6:u64` | `7:0b1010` suffix `u64` |
| `0o644u32` | `1:0o644` \| `6:u32` | `7:0o644` suffix `u32` |
| `0o755_u32` | `1:0o755_` \| `6:u32` | `7:0o755` suffix `u32` |
| `0x1010u64` | `7:0x1010` suffix `u64` (already correct) | unchanged |

Note the underscore form also left a trailing `_` inside the literal text.

This is not a hypothetical syntax — both forms are used in tree:
`src/os/apps/coreutils/cp.spl:15` (`0o644u32`),
`src/os/apps/coreutils/mkdir.spl:13` (`0o755u32`),
`test/01_unit/os/posix/signal_compat_spec.spl:17` (`0b1010u64`),
`test/01_unit/lib/common/zstd_fse_huffman_weight_encode_spec.spl:75` (`0b10110u64`).

## Defect 2 — `for i in 0..64` capped every radix digit run

All three radix branches used a bounded `for i in 0..64` where the decimal
branch used `while true`. A 64-bit literal written with underscore separators
is longer than 64 characters after the prefix, so the loop stopped mid-digit-run
and split one literal into two INT tokens:

```
0b11111111_00000000_11111111_00000000_11111111_00000000_11111111_00000001
```
lexed as `1:0b11111111_..._11111111_0` | `1:0000001`.

## Fix

`src/compiler/10.frontend/core/lexer_struct.spl`, `scan_number`: give the `0b`
and `0o` branches the same suffix scan the hex branch has (including the
`make_token` → `core_token_suffix_save` ordering that `core_token_capture`'s
unconditional suffix reset requires), and replace all three `for i in 0..64`
digit loops with `while true`.

## Blast radius

The fix flips suffixed binary/octal from `TOK_INT_LIT` (1) to
`TOK_SUFFIXED_INT` (7). Both consumers in
`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` — `:353`
(`expr_int_lit`) and `:365` (`expr_suffixed_int`) — call the same
`parse_int_literal_text` (`:156`), which is radix-aware for `0x`/`0b`/`0o` and
strips `_`. So the kind flip cannot trade a loud token-split for a silent wrong
value.

## Verification

`test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl` — 9 examples.
The two hex rows are the discriminator: same accessors, same call shape, already
green, so a failure confined to the `0b`/`0o` rows cannot be a harness artifact.

- RED (origin/main lexer): `executed=9 passed=4 failed=5 dropped=0`, exit 1.
- GREEN (fixed lexer): `executed=9 passed=9 failed=0 dropped=0`, exit 0.
- Sabotage: restoring `origin/main`'s `lexer_struct.spl` in place reproduces the
  RED verdict; restoring the fix returns GREEN.

Collateral slice: `test/01_unit/compiler/lexer` — 50 total, 48 passed, 2 failed.
The 2 failures are `lexer_triple_quote_docstring_spec.spl`, which reports the
identical `executed=7 passed=5 failed=2` on origin/main's unmodified lexer —
**pre-existing, not caused by this change** (baselined by swapping the file and
re-running).

### Differential token-stream check on real in-tree sources

A throwaway spec lexed four real files with CoreLexer and printed
`tokens=<n> h=<digest-of-(kind,text,suffix)-stream>`, once with the fixed lexer
and once with `origin/main`'s. This is both the impact evidence and the
collateral-damage bound:

| file | before | after |
|---|---|---|
| `src/os/apps/coreutils/cp.spl` (has `0o644u32`) | `tokens=252 h=672831186` | `tokens=251 h=911838769` |
| `src/compiler/10.frontend/core/parser_expr.spl` | `tokens=9347 h=502690997` | identical |
| `src/compiler/10.frontend/core/types.spl` | `tokens=9024 h=350861240` | identical |
| `src/lib/common/text.spl` | `tokens=491 h=229556861` | identical |

`cp.spl` loses exactly one token — the spurious `IDENT("u32")` the split used to
produce — confirming a real in-tree file was mis-lexed. The three control files
carry no radix-suffixed literal and are byte-identical in both token count and
digest across 18,862 tokens, so the change is inert outside its intended input
class.

## Not fixed (recorded, out of scope)

The octal branch accepts `8` and `9` (`is_digit(oc)` rather than an octal-digit
test), so `0o789` lexes as a valid octal literal and
`parse_int_literal_text` evaluates it with base-8 arithmetic on out-of-range
digits. Closing it needs a new lexer error path, not a scanner tweak.
