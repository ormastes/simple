# native-build: MIR lowering has no `to_u8` or `join` — the typed crypto path cannot be built natively

> **STATUS 2026-08-08 (later): `to_u8` family FIXED+VERIFIED, `join` FIXED+VERIFIED.
> Open siblings: `slice`, `merge` (declined, see below), plus one fail-open defect
> introduced and corrected in the same session. Read "Resolution" at the bottom
> first — the sections above it are the original filing and are now historical.**

**Filed:** 2026-08-08 · **Severity:** high (blocks native verification of landed
security fixes; not a wrong-answer bug but a cannot-build bug) · **Lane:** pure-Simple
`native-build` (bare-positional entry, i.e. the real self-hosted `CompilerDriver`, not
the `--entry` path that delegates to the Rust runtime).
**Interpreter and seed JIT: both CORRECT.** Only native codegen fails.

## Summary

Two method calls are unimplemented in MIR lowering and abort the native build:

```
error: MIR lowering error: unresolved method call: to_u8
error: MIR lowering error: unresolved method call: join
```

This is **not** a wrong-value defect. The build fails outright (`RC=1`, no binary), so
any code on these paths simply cannot be exercised under native codegen.

## Minimal reproduction (dependency-free — no stdlib crypto involved)

`.nvprobe2/mir_gap.spl`:

```simple
fn main():
    val b = (255 & 0xFF).to_u8()
    print("CHK to_u8_ok")
    var parts: [text] = ["a", "b"]
    print("CHK join=" + parts.join(","))
    print("CHK done=1")
```

| lane | result |
|------|--------|
| `SIMPLE_EXECUTION_MODE=interpret` | `CHK to_u8_ok` / `CHK join=a,b` / `CHK done=1` |
| `bin/simple native-build <entry>` | `RC=1`, no binary, both methods unresolved |

The probe deliberately imports nothing, to prove the gap is general rather than an
artifact of a particular module or of a larger probe.

## Why this matters — it blocks verification of landed security fixes

Both methods are load-bearing in code that landed 2026-08-07/08 carrying an
"interpreter-only" caveat, so that caveat **cannot currently be discharged natively**:

- **`to_u8`** — `src/lib/common/aes/modes.spl:31` (`_i64_to_u8`, the `[i64]`→`[u8]`
  bridge that *every* `aes_cbc_encrypt` / `aes_cbc_decrypt` / `aes_ctr_*` entry point
  calls, at lines 60/74/167/189/214/231) and **28 occurrences** in
  `src/lib/common/crypto/aes_gcm.spl`. The entire typed AES path is unbuildable
  natively. This is the direct blocker on the native half of
  `credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`
  (fix `23839a41331`).
- **`join`** — `src/lib/nogc_sync_mut/database/sql/escape.spl:20,33,122`, i.e.
  `quote_ident` and its siblings, which are exactly the identifier-quoting path added by
  the SQL savepoint injection fix `021f5171208`.

So two landed security fixes are verifiable on the interpreter and the seed JIT, and
**not verifiable at all** on the pure-Simple native lane until these lowerings exist.

## What this is NOT

Not a native-build outage. `native-build` is working: a sibling probe
(`.nvprobe/scope_id.spl`) built and ran successfully (`RC=0`, 30 KB binary) in the same
window under load ~60–92. The earlier "total native-build outage" report was already
refuted by `a9c8effc054`; this is two specific missing method lowerings, nothing wider.

## Note on diagnostics

The failing log still contains `[stderr truncated by native-build entry]` even after
`a9c8effc054`. The load-bearing `error:` lines survived in this instance, but the marker
means a truncation path is still live — do not trust a `grep -c` over native-build
stderr to be exhaustive; read the preserved-diagnostics region.

---

# Resolution (2026-08-08)

## The failing family — measured, not assumed

One probe carrying eight typed-receiver method calls through plain `native-build`
(`self.error` at `method_calls_literals.spl` COLLECTS and continues, so a single build
enumerates the whole family) split the names cleanly:

| method | typed receiver | before | after |
|--------|----------------|--------|-------|
| `to_u8`/`to_u16`/`to_u32`/`to_u64`/`to_i8`/`to_i16`/`to_i32`/`to_i64`/`to_f32`/`to_f64` | i64 | unresolved | **FIXED** (`3fec678b29a`) |
| `join` | `[text]` | unresolved | **FIXED** (this session) |
| `contains` | `[i64]` | unresolved | **FIXED** (this session, array receiver only) |
| `index_of` | `text` | unresolved | still loud — fix attempted and REVERTED, see below |
| `slice` | `[i64]` | unresolved | **still loud, declined** |
| `merge` | array/dict | unresolved | **still loud, declined** |
| `substring`, `split`, `replace`, `unwrap` | text / Option | **already worked** | already worked |

Root cause of the fixed group is ONE mechanism, not N: builtin types (numeric, Array)
carry no symbol-bearing HIR type, so `try_instance_method` / `try_trait_method` /
`try_ufcs` in `resolve_strategies.spl` all decline and every such call lands in
`case Unresolved:` with no arm. `join` had a working arm already — it was gated behind
`SIMPLE_BOOTSTRAP=1`, an env check that was only ever a proxy for "no type info" and
that excluded the identical normal-path gap. (Exactly the same mistake had already been
found and corrected for `len` in the same file.) The fix keys the arm off
`resolution == Unresolved` instead, which is strictly narrower on the bootstrap lane and
refuses to hijack a genuinely resolved user-defined `join`.

`slice` and `merge` are declined for a shared, documented reason: both return a fresh
collection HANDLE that must be registered in the lowering's runtime-value bookkeeping
before a downstream `.len()`/index read works. That is a larger change than a one-call
arm; adding the call without the bookkeeping would trade a loud failure for a wrong
value. They stay loud-failing.

## RED→GREEN, with values (not build-only)

A build-only check is exactly what this defect class defeats, so every check runs the
produced binary and diffs against the interpreter oracle.

- **Conversions** — native binary produced (28,976 B), `RC=0`, output
  `255 / 44 / 255 / 0 / 4464` — byte-identical to the interpreter oracle, including the
  signedness cases the lowering claims (u8 zero-extends `-1 → 255`, i32 sign-extends
  `4294967296 → 0`). `SIMPLE_MIR_LOG_CONV=1` printed 5 `[conv-lower] narrowing
  conversion arm hit` lines, positively proving the executing lowering is the source
  being read.
- **`join` / `contains`** — RED: build `RC=1`, no binary, `unresolved method call: join`.
  GREEN: build `RC=0`, binary runs `RC=0`, `J1=a,b`, `CT1=true`, `CT2=false` — all
  matching the oracle, with `[conv-lower] join arm hit` proving edit visibility.

## A fail-open defect was introduced here and corrected — record it

The first cut of the new arm also routed `index_of` to `rt_index_of` and accepted
text/dict receivers. The resulting native binary returned
`"hello world".index_of("world")` == **-1** where the oracle says **6**: a WRONG-VALUE
defect, strictly worse than the loud build failure it replaced. It reached `origin/main`
before it was caught, swept in by a parallel session's whole-WC sync commit
(`4af5b26a2e4 chore: sync and pre-push cleanup`) — a concrete instance of the
"chore-labelled bulk commits hide semantic changes" hazard.

Root cause: `rt_index_of` calls `rt_array_index_of` on the raw receiver word and falls
back to `rt_string_find`; at this point in lowering the text receiver and/or the literal
needle are NOT in the tagged representation those helpers expect (a bootstrap string
literal lowers to a RAW `char*` — the `starts_with` arm in the same file has to call
`rt_string_new` to tag it first).

**Transferable lesson: the receiver-polymorphic runtime accessors are NOT uniformly safe
to call from this arm.** `rt_contains` on a tagged runtime array is verified correct;
`rt_index_of` on a text receiver is verified wrong. Only verify-then-ship, per receiver
class. Corrected in `469517642cd`.

## Downstream: the AES native build is now ONE name from green

`aes_cbc_encrypt` + `aes_cbc_decrypt` round-trip, built through the real self-hosted
`CompilerDriver`: the build now clears `to_u8` and `join` entirely and fails on exactly
one remaining unresolved name — **`merge`** (2 occurrences, reached transitively, not
from the AES sources themselves). Interpreter oracle for that probe is pinned at
`CT_LEN=32 CT_SUM=4056 ROUNDTRIP_OK=1`. The native AES caveat therefore remains OPEN,
but its blocker list is down from `{to_u8, join, merge}` to `{merge}`.

## This is NOT the Stage-3 root cause — and Stage-3 is not one family

`stage3_vacuous_binary_..._2026-08-08.md` reports 3,629 `const-0 placeholder`
substitutions over 538 distinct names, keyed on the same `"unresolved method call:"`
string. The measurement above shows those 538 names are **at least two different
mechanisms**:

- A small set genuinely has no lowering: `merge` (#2 at 248), `slice` (#3 at 242), and
  `join` before this fix.
- A much larger set — `substring` (#1 at 261), `unwrap` (#4 at 217), `split`, `replace` —
  **already lowers correctly under plain `native-build` on a typed receiver.** Those
  names can only be failing in Stage 3 because Stage 3's flat HIR erases receiver types
  and dumps everything into the `Unresolved` arm.

So adding lowering arms cannot fix the second group, which is the majority. The Stage-3
work item is whatever loses the receiver types upstream, not 538 missing lowerings. The
shared error string is a red herring. (The 3,629 figure was deliberately not re-measured:
a Stage-3 run costs >1200s and the discriminating evidence above is cheaper and
sharper.)
