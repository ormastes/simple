# Bug: flat `i64?` optional lane collides with tagged-value scheme (seed JIT) — payload 3 reads as nil

Status: OPEN — root-caused 2026-07-22; architectural fix required
Observed: 2026-07-22 (as "index_of digit-leading literal" — that was a red herring, twice)
Severity: P1 — silently wrong values in production tooling paths (JIT `run` on
seed-engine binaries, which includes the currently deployed bin/release binary)

## True root cause (isolated, no strings involved)
The seed JIT's **flat (non-boxed) `i64?` lane** does not apply the runtime's
tagged-value scheme (`(v<<3)|tag`), but its values flow into consumers that
dispatch on tag bits. Nil is `rt_core_nil()` = bit pattern **3**
(src/runtime/runtime_native.c ~2402-2422 — the sentinel was moved 0→3 to fix
`native_i64opt_some0_collapses_to_nil`, which only relocated the collision).

Decisive isolation (`fn make_opt(v: i64) -> i64?: return v`, seed JIT):

```
make_opt(0) → some:0          (ok — 0 coincidentally reads as tagged int 0)
make_opt(1) → some:nil        (payload 1 misread via tag bits)
make_opt(2) → some:0.0        (payload 2 misread as float tag)
make_opt(3) → NIL             (payload 3 == nil sentinel — value LOST)
make_opt(4) → some:<value:0x4> (raw repr fallback)
make_opt(11) ?? -99 → prints "true" (11&7=3 tag misread downstream)
```

`SIMPLE_EXECUTION_MODE=interpreter` is CLEAN (real Rust Value enum, no packing).

## Surface symptoms (how it was found)
`text.index_of(needle)` "returns nil for any match at position 3" — because the
found index 3 IS the payload-3 collision. All string-search implementations
(spl_str_index_of, rt_string_find, SIMD family) verified CORRECT. Earlier
"digit-leading literal" and "position 3 search miss" characterizations were
both artifacts of this. Every `i64?`-returning API (find/rfind/index_of/
last_index_of/dict lookups/...) mis-nils on payload 3 and misprints small
payloads.

## Affected engines / binaries
- Seed JIT (`run` default): AFFECTED — confirmed. Note the wt_e2ebootstrap
  "full" binary delegates run to a sibling `simple_seed`; the deployed
  bin/release/x86_64-unknown-linux-gnu/simple is ALSO seed-engine (banner) and
  reproduces — consistent with the known "self-hosted not deployed" blocker.
- Interpreter: NOT affected — confirmed.
- Seed native/LLVM codegen: untested, likely affected (same dispatch tables,
  codegen/llvm/functions.rs:2190/2527, llvm/emitter.rs:169/191) — prediction,
  not verified.

## Blast radius (grep evidence)
- 45 sites compare find/index_of results raw (`>=0`/`==-1`).
- 429–1609 sites coalesce via `??` — silently take the nil branch when the true
  answer is 3 (production compiler .spl code incl. linker/backend).

## Fix direction (senior call: architectural, do NOT spot-patch)
A boundary-boxing patch at index_of call sites was attempted and PROVEN WRONG
(`??` does not un-shift; would corrupt all 429 sites — dead-end diffs kept in
session scratchpad for reference). Correct options:
(a) apply the real `<<3` tagging to the flat `i64?`/`bool?` lane end-to-end
    (principled; every producer/consumer must be audited), or
(b) INT64_MIN-style sentinel for the flat lane (smaller change but does NOT fix
    the tag-misread symptoms for payloads 1/2/4/5 — insufficient alone given
    the make_opt matrix above).
Given (b) is demonstrably insufficient, the fix is (a) or removing the flat
lane. Needs a dedicated seed change with the make_opt(0..12) matrix + index_of
matrix + `??`/`.?`/print consumers as the regression gate.

## Related prior filings (same family)
- native_i64opt_some0_collapses_to_nil (the 0-sentinel ancestor)
- seed BoxInt <<3 enum heap-handle mangling (stage4 wall)
- interpreter quirk ".? on 0-i64 → false" — likely the same lane, old sentinel
