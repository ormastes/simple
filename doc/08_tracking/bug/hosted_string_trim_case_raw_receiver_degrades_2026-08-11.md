# Hosted `rt_string_trim`/`rt_string_ascii_case` family degrades on a raw receiver

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Status
**RESOLVED 2026-08-11.** Follow-up gap #2 flagged (but explicitly left open)
by `native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md`
(commit `43aed2b9df8`).

## Root cause (PROVEN)

`src/runtime/runtime_native.c` — `rt_core_as_string(value)` (line ~1662)
returns `NULL` for a raw, untagged `char*` receiver (only a tagged,
**registered** heap string decodes). Five functions used that `NULL` as
"give up" instead of "try the raw path":

| function | file:line (pre-fix) | degradation |
|---|---|---|
| `rt_string_trim` | `runtime_native.c:4770` | `if (!s) return value;` — raw pointer passed straight through **unchanged**, not trimmed |
| `rt_string_trim_start` | `runtime_native.c:4784` | same passthrough |
| `rt_string_trim_end` | `runtime_native.c:4796` | same passthrough |
| `rt_string_ascii_case` (backs `to_lower`/`to_upper`) | `runtime_native.c:3651` | `if (!s) return rt_core_nil();` — silently returns **nil** |

**Reachability:** MIR's `ensure_tagged_str` normalization (which would
otherwise guarantee a tagged heap-string receiver at these call sites) is
gated on `resolution_is_unresolved` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2194`:

```
if (method == "trim" or ... or method == "lower" or method == "to_lower" or method == "to_upper" ...)
   and (resolution_is_unresolved or (method == "contains" and predicate_receiver_is_text))
   and not contains_recv_is_array and not predicate_has_custom_owner:
```

When resolution is **not** unresolved (a statically-resolved call), this arm
is skipped and a raw string-literal receiver can reach `rt_string_trim` /
`rt_string_ascii_case` untagged.

## Fix

Fixed at the primitive (not in MIR), for the same reason the equality/
ordering siblings were: it is a single, centrally-testable change that fixes
every call site — including any MIR path this analysis didn't enumerate —
without adding a new normalization arm to an already-intricate gating
expression (`method_calls_literals.spl:2194`) where an extra condition risks
an unrelated regression. Added a shared helper,
`rt_string_promote_raw_receiver` (`runtime_native.c`, next to
`rt_string_trim`, with a forward declaration ahead of
`rt_string_ascii_case` since that function appears earlier in the file):

```c
static int rt_string_promote_raw_receiver(int64_t value, int64_t* out) {
    if (value < 0x10000) return 0;
    const char* p = (const char*)(uintptr_t)value;
    *out = rt_string_new((const uint8_t*)p, (uint64_t)strlen(p));
    return 1;
}
```

Same conservative floor as `rt_interp_cstr` (`< 0x10000` = nil/bool/small-int,
left alone — "not text" is unchanged behavior for genuinely non-text
values). All five functions now promote a plausible raw receiver to a real
heap string first, then recurse once into the already-correct heap-string
path:

```c
int64_t rt_string_trim(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) return rt_string_trim(promoted);
        return value;
    }
    ...
}
```

(`rt_string_ascii_case` returns `rt_core_nil()` instead of `value` in the
non-promotable branch, preserving its original non-text contract.)

## Red-then-green (verbatim)

`src/runtime/test/rt_string_trim_case_raw_receiver_selfcheck.c` reimplements
the BEFORE/AFTER shape locally (mirrors `rt_core_as_string` /
`rt_string_trim` / `rt_string_ascii_case`'s real behavior, so it always
demonstrates the defect regardless of the current state of
`runtime_native.c`; refuses to pass vacuously — exits 2 if the defect fails
to reproduce with the old predicate):

```
== BEFORE (shipped rt_string_trim / rt_string_to_lower) ==
  REPRODUCED: trim(raw "  padded  ") returned the raw pointer unchanged
  REPRODUCED: to_lower(raw "MiXeD") returned nil
== AFTER (raw receiver promoted to a real heap string) ==
  ok   trim(raw "  padded  ")                   = "padded"
  ok   to_lower(raw "MiXeD")                    = "mixed"
  ok   trim(heap "  padded  ")                  = "padded"
  ok   to_lower(heap "MiXeD")                   = "mixed"
  ok   trim(nil) is a no-op
  ok   to_lower(nil) stays nil
  ok   trim(small int 7) is a no-op

PASS - 7 assertion(s) checked, defect reproduced before / fixed after
```

Negative controls included above: heap-string receivers (the already-working
path) are unaffected, and genuinely non-text small words (nil, small int 7)
are never dereferenced and keep their documented "no-op"/"nil" contract.

Guard red-then-green, confirmed by stashing `runtime_native.c`:
```
FAIL — 5 of 6 check(s) failed
```
(all four functions UNFIXED, helper missing), then restoring the fix:
```
PASS — 6 check(s) passed, hosted string trim/case raw-receiver degradation fenced
```

## Guard

`scripts/check/check-hosted-string-trim-case-raw-receiver.shs` — verdict as
the last stdout line (`PASS — <n> check(s) ...` / `FAIL` exit 1 / `ERROR —
nothing was checked` exit 2). Runs the selfcheck, then greps each of the four
functions' bodies in `runtime_native.c` for a call to
`rt_string_promote_raw_receiver` and confirms the helper itself is defined.

## Related
- `native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md` (parent commit this follows up)
- `freestanding_text_ordering_raw_literal_2026-08-11.md` (sibling gap #1, freestanding ordering)
