# sha256_bytes / base58check engine divergence — root cause (2026-07-29)

Assignment (Fix-Security-Inline, top priority): root-cause the pass-7
finding that `sha256_bytes` / `_b58_double_sha256_first4` produced
different digests under the two engines for identical input.

## Pinned truth (independent of this repo, re-derived, never from memory)

python3 `hashlib` was used as the sole oracle throughout — never a
from-memory "canonical" constant (per the repo's standing fabricated-KAT
incident):

```
SHA-256("")                                       = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
SHA-256("abc")                                     = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
SHA-256(NIST 2-block-boundary 56-char vector)      = 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
SHA-256(135-byte multi-block "quick brown fox"x3)  = dc985401a68faff03051c78bbf32bb2fd27ba216b0dba19b050b936d534b8ba9
```

## Step 1 result: `sha256_bytes` / `sha256_text` themselves are CORRECT under both engines

Calling `sha256_bytes([i64])` and `sha256_text(text)` directly against all
4 vectors above: byte-exact match against the python reference, identical
under both the default engine and `SIMPLE_EXECUTION_MODE=interpret`. **The
hash function's own arithmetic (message schedule, compression rounds,
`rotr32`, `u32` wrap-mask via `& 4294967295`) is not the bug** — none of
the coordinator's suspected families (b) empty-list-rebind, (c) compound-
assign drop, (d) u32 rotation lowering apply here; `sha256_bytes`'s `w`
array is a pre-sized `[i64] = [0; 64]` typed literal, never pushed/grown,
never rebound.

## Step 2 result: the bug is in `base58.spl`'s own helper functions — a third trigger for the pass-7 `<<3` tag-box family

Bisected the real call chain
(`_b58_double_sha256_first4` → `_b58_u8arr_to_list` → `sha256_bytes` (x2)
→ `_b58_list_get_byte`) with a 4-variant probe:

| Step | Shape | Default engine |
|---|---|---|
| `sha256_bytes(list_arg)` where `list_arg` built via `.push()` (untyped `list` → `[i64]` param) | list-to-typed crossing | correct |
| single-hash result read via direct bracket index `h1[i]` | no crossing | correct |
| single-hash result read via `_b58_list_get_byte(l: list, i)` | **`[i64]`-typed value passed into a `list`-typed PARAMETER** | **wrong** |
| double-hash (`sha256_bytes(sha256_bytes(...))`) read via direct index | no crossing | correct |
| double-hash read via `_b58_list_get_byte` (matches real code) | same crossing | **wrong** |

This pinned the bug to `_b58_list_get_byte(l: list, i: i64) -> i64: l[i] &
0xFF` — reading `l[i]` **inside a callee whose parameter is declared with
the untyped `list` type**.

**Further isolation (sha256-free minimal repro)** proved the trigger is
the callee's PARAMETER TYPE, not the caller's argument shape:

```
fn get_via_list_param(l: list, i: i64) -> i64:
    l[i] & 0xFF

fn get_via_typed_param(l: [i64], i: i64) -> i64:
    l[i] & 0xFF

val typed: [i64] = [10, 20, 30, 40]
var untyped = []          # built via .push(10)/.push(20)/.push(30)/.push(40)
```

| Call | Default engine | Expect |
|---|---|---|
| `get_via_list_param(typed, i)` | `80,160,240,64` | `10,20,30,40` |
| `get_via_typed_param(typed, i)` | `10,20,30,40` (correct) | `10,20,30,40` |
| `get_via_list_param(untyped, i)` | `80,160,240,64` | `10,20,30,40` |
| `typed[i]` direct, no call at all | `10,20,30,40` (correct) | `10,20,30,40` |

**Both** a typed `[i64]` argument AND a genuine untyped `list` argument
built via `.push()` are corrupted equally when read through a `list`-typed
formal parameter (`80 = 10<<3`, `160 = 20<<3`, `240 = 30<<3`, `64 = (40<<3)
mod 256`) — the exact same `<<3` tag-box shift characterized in the
pass-7 base58_decode root-cause doc
(`doc/08_tracking/bug/base58_decode_reversed_polarity_rootcause_2026-07-29.md`),
but with a **third, independent trigger**: pass-7 found (1) empty-list-
first-assignment-then-rebind and (2) loop-carried push-realloc spill; this
pass adds (3) **any function parameter typed as the untyped `list`
corrupts bracket-index reads of its argument inside the callee, under the
default engine, regardless of the argument's own concrete type or
construction.** Interpreter is unaffected by all three triggers.

## WHICH engine, WHICH function

**Default engine (JIT/native codegen) is wrong; interpreter is correct** —
same polarity as pass 7's base58_decode finding, opposite of the
majority-pattern byte/char-index campaign. The wrong function is
`_b58_list_get_byte` (site of the sha256-checksum-visible divergence) and,
found while auditing the rest of the file for the same parameter shape,
also `_b58_list_all_zero` (see below — a second, independently confirmed,
real, previously-undetected bug, not hypothetical).

## Second real bug found by the same audit: `base58_encode` silently truncates for specific byte values

`_b58_list_all_zero(lst: list) -> bool` has the exact same `list`-typed-
parameter shape. `base58_encode`'s digit-collection loop calls
`_b58_list_all_zero(work)` to decide when all digits are consumed. Under
the default engine, for any byte value `v` where `(v<<3) mod 256 == 0`
(i.e. `v` is a multiple of 32: 32, 64, 96, 128, 160, 192, 224), the
corrupted read makes a **nonzero** element look like zero, so the "all
digits consumed" check fires prematurely.

**Confirmed with real, previously-undetected corruption** (verified
against an independent python3 base58 encoder):
- `base58_encode([32])` returned `""` (empty!) under the default engine,
  should be `"Z"`.
- `base58_encode([64])` returned `""`, should be `"27"`.
- **The repo's own pre-existing spec fixture is a casualty**: the
  canonical Bitcoin-wiki P2PKH test vector already present in
  `test/01_unit/lib/common/encoding/base58_spec.spl`
  (`_check_encode_p2pkh`, payload
  `010966776006953D5567439E5E39F86A0D273BEE`, version 0) encoded to
  `16UwLL9Risc3QfPqBUvKofHmBQ7vQZvtX` under the default engine instead of
  the correct `16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM` — a **wrong Bitcoin
  address**, silently, from a well-known reference vector already checked
  into this repo. This spec has been passing "green" only because
  `bin/simple test` forces `SIMPLE_EXECUTION_MODE=interpret`
  (documented harness divergence,
  `doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`)
  and therefore never exercised the default engine this bug lives in.

## Fix (base58-side workaround, contained — no compiler change)

`src/lib/common/encoding/base58.spl`: eliminated the untyped `list` type
from the file entirely (all three remaining uses shared this exact
trigger), retyping to concrete `[i64]`:
- `_b58_list_all_zero(lst: list) -> bool` → `_b58_list_all_zero(lst: [i64]) -> bool`
- `_b58_u8arr_to_list(bytes: [u8]) -> list` → `_b58_u8arr_to_list(bytes: [u8]) -> [i64]` (its internal `var l = []` → `var l: [i64] = []`)
- `_b58_list_get_byte(l: list, i: i64) -> i64` → `_b58_list_get_byte(l: [i64], i: i64) -> i64`
- `base58_encode`'s `var work = []` → `var work: [i64] = []` (to match `_b58_list_all_zero`'s new signature; `work` is built via `.push()` entirely BEFORE the digit-collection loop starts and never grown inside it, so this does not reintroduce pass-7's loop-carried-spill trigger)

No rebinding, no cross-iteration `.push()`, and no `list`-typed parameter
remain anywhere in the file.

## Verification (both engines)

All of the following are byte-exact / string-exact identical under the
default engine and `SIMPLE_EXECUTION_MODE=interpret`, and match
independently-derived python3 references:

- The 4 pinned SHA-256 vectors (unchanged by this fix — `sha256_bytes`
  itself was never broken).
- `base58_decode` matrix (8 cases, unchanged from pass 7).
- `base58_encode`/`base58_decode` round-trip: `[32]`, `[64]`, `[96,5]`,
  `[]`, `[0]`, `[0,0,0]`, and 5/25/100-byte pseudo-random payloads — all
  `match=true`.
- `base58check_encode(payload, 0)` for the 20-byte payload used in pass 7
  now produces `12J13oCScQMK7FrgunG1W46MUZ3Fg3EGbD` under **both** engines
  (was `...Ff6fpqd` under the default engine pre-fix), matching the
  independent python3 double-SHA256 + base58 reference exactly.
- The repo's own canonical P2PKH vector re-verified directly (not via
  `bin/simple test`, which cannot see the default engine): now
  `16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM` under the default engine, matching
  the spec's existing expectation and the Bitcoin-wiki reference.

## Vacuity

Swapped the original (pre-pass-8) `base58.spl` back in and re-ran the
regression probe under the default engine: `base58_encode([32])` /
`([64])` round-trips both fail (`match=false`), and
`base58check_encode` on the pass-7 payload reproduces the exact wrong
address (`...Ff6fpqd`) from pass 7 — confirming the fix is real and the
before/after delta is the genuine signal, not a probe artifact. Restored
the fix afterward and re-confirmed byte-identical to the landed state.

## Spec / regression coverage

Added two `it` blocks to
`test/01_unit/lib/common/encoding/base58_spec.spl`
(`_enc_multiple_of_32_a`/`_b`, values `[32]`→`"Z"` and `[64]`→`"27"`) to
pin the expected values. Note: `bin/simple test` forces interpret mode
(documented harness divergence) and therefore **cannot** by itself catch
a regression of this exact bug (the interpreter was never wrong here) —
this doc's direct-execution, both-engine probe transcript above is the
actual proof; the spec exists to pin the expected values for whichever
future tooling can exercise the default engine.

## Campaign status

Closes the sha256_bytes/base58check engine-divergence item flagged as
"new, unowned" at the end of the pass-7 base58_decode root-cause doc.
Both defects (checksum corruption in `_b58_list_get_byte`, silent
encode-truncation in `_b58_list_all_zero`) are fixed and verified.
Remaining open item from the wider campaign: the kafka `list.get(i)`
tag-box bug (pass 3), which stays with the engine investigation lanes —
now with three named triggers for the same `<<3` family on record
(empty-list-rebind, loop-carried push-realloc spill, `list`-typed
parameter) for whoever picks up the compiler-side (cranelift) fix.
