# rt_clear Dict-arm misclassification hypothesis: REFUTED by direct C measurement

- **Date:** 2026-08-17
- **Status:** hypothesis REFUTED. No product code change landed. Evidence
  harness + fail-closed guard landed.
- **Related:** `8510a8368ca2` (added the Dict arm to `rt_clear`),
  `dd1c0525c5b` (`check-dict-engine-differential.shs`),
  `native_build_source_closure_zero_sources_2026-08-17.md` (the blocked
  `native-build` path this work routed around).

## The hypothesis under test

`8510a8368ca2` fixed `Dict.clear()` from a silent no-op to a real clear,
taking bootstrap stage-3 errors from 7,069 to 0 — but stage 3 then SIGSEGVed
(exit 139) at parse file 1/619. The proposed mechanism was **misclassification**
in the C runtime: `rt_core_is_registered_dict` (`src/runtime/runtime_native.c`
:1074-1076) is registry-membership ONLY, with no `kind` check, whereas its
sibling `rt_core_is_registered_array` (:1083-1086) has an explicit
`kind == RT_VALUE_HEAP_ARRAY` test. The inference was that a non-dict receiver
would be admitted into the new Dict arm and `rt_dict_clear` would walk
`d->cap` entries at dict field offsets over a smaller object — a wild write.

## Method

`bin/simple native-build` is unusable on a small fixture right now
(`BUILD_RC=255`), so the predicates were measured directly: a single-TU C
harness that `#include`s `runtime_native.c`, making the file-static predicates
(`rt_core_as_dict`, `rt_core_is_registered_dict`,
`rt_core_registered_object_kind`) observable. Loud cases run in a forked child
because `rt_refuse_non_text_receiver` calls `exit(70)`.

- Harness: `test/harness/rt_clear_receiver_dispatch_harness.c`
- Link stubs: `test/harness/rt_clear_harness_stubs.c`
- Guard: `scripts/check/check-rt-clear-receiver-dispatch.shs`

## Measurements (applied arm, md5 `38a93f795277dd405362a5b14af9a599`)

```
sizeof(RtCoreArray)=32 sizeof(RtCoreDict)=40 offsetof(dict.entries)=32 offsetof(dict.cap)=8
[ ok ] C1 dict receiver clears                len 5 -> 0 (want 5 -> 0)
[ ok ] C2 array receiver: dict arm NOT taken  as_dict admits=0 len 6 -> 0 (want 6 -> 0)
[ ok ] C3 wide-int (RT_VALUE_HEAP_INT)        kind=0x494e5431 byte0=0x31 registered=1 is_registered_dict=1 as_dict=0
[ ok ] C4 boxed u64 (RT_VALUE_HEAP_UINT)      kind=0x55494e54 byte0=0x54 registered=1 is_registered_dict=1 as_dict=0
[ ok ] C5 heap float (RT_VALUE_HEAP_FLOAT)    kind=0x464c5431 byte0=0x31 registered=1 is_registered_dict=1 as_dict=0
[ ok ] C6 non-collection receiver stays loud  child rc=70 (want 70 = loud refusal; 0 = SILENT NO-OP defect)
stomped_array: as_dict=0x5e03cbc67ce0 cap=4 entries=(nil)
[ ok ] C7 stomped-kind array (descriptive)    child rc=0 (survived) [descriptive: pre-corrupted kind byte]
PASS — 7 rt_clear receiver-dispatch case(s) checked
```

### What this establishes, as measurement not inference

1. **The predicate asymmetry is real** — `is_registered_dict=1` on a wide-int, a
   boxed u64 and a heap float, none of which is a dict. The brief was right
   about the shape of the code.
2. **The asymmetry is harmless, and the proposed fix is a behavioural no-op.**
   `as_dict=0` in every one of those cases: `rt_core_as_dict` (:7936-7943)
   performs `d->kind != RT_VALUE_HEAP_DICT` on the line immediately AFTER the
   registry test, and that check catches every non-dict. **The Dict arm of
   `rt_clear` is never entered by a non-dict receiver.** Moving the kind check
   up into `rt_core_is_registered_dict` would change no observable behaviour,
   so it cannot be the companion fix. Nothing was landed on that basis.
3. **Fail-closed behaviour is preserved.** C6 measures `rc=70` — a
   non-collection receiver is still refused loudly. The Dict arm did not
   convert a loud refusal into a silent no-op.
4. **C7, the one genuinely informative corrupted case:** an array with its kind
   byte pre-stomped to `0x06` IS admitted by `as_dict`, and `cap` then reads
   `4` — the array's `len`. `entries` reads offset 32, one word PAST the
   32-byte array allocation, and read back `(nil)` here, so
   `rt_dict_clear`'s `if (!d->entries) return 0` caught it and the child
   survived. The overlap the brief described is real, but it requires memory
   corruption to have ALREADY happened, and no predicate can distinguish a
   stomped kind byte from a genuine dict. This is descriptive in the harness,
   never asserted as pass/fail.
5. **The Rust side has no such asymmetry, so there is nothing to fix there.**
   `collections.rs:3225-3238` dispatches via
   `get_typed_ptr::<RuntimeDict>(receiver, HeapObjectType::Dict)` — explicitly
   type-checked, symmetric with the Array arm.

## Ablation (mandatory, distinct binaries)

| arm | md5 | verdict |
|---|---|---|
| Dict arm applied | `38a93f795277dd405362a5b14af9a599` | `PASS — 7 rt_clear receiver-dispatch case(s) checked` (rc 0) |
| Dict arm removed | `2ef508bf135d8b922bd29b5b48f692b1` | harness dies at C1, `REVERTED_HARNESS_RC=70` |

The reverted arm's failure mode is itself evidence: with the Dict arm removed,
a dict receiver falls through to `rt_refuse_non_text_receiver` and the process
exits **70**. The md5s differ, so the two arms are genuinely distinct binaries.

## The strongest narrowing this produced

Pre-fix, the **C** lane exited **70** on a `Dict.clear()` — measured above, not
inferred. But pre-fix stage 3 produced 7,069 *errors* and completed 619/619
parses; it did not exit 70. A silent no-op on `Dict.clear()` is the **Rust**
runtime's pre-fix behaviour, not the C runtime's. Therefore **stage 3 was
exercising the Rust runtime, and the C-side predicate asymmetry cannot be the
cause of the exit-139.** Whoever picks this up should look at the Rust lane, and
should treat "a latent unhandled-miss path in the compiler, unmasked now that
stale dict entries are correctly discarded" as the leading remaining
hypothesis — that shape fits "errors go to 0 AND a new crash appears" better
than any runtime memory bug found here.

This is a narrowing, not a diagnosis. It is not proven.

## Guard

`sh scripts/check/check-rt-clear-receiver-dispatch.shs --selftest`

Verdict is the last stdout line; 0 cases checked is `ERROR` exit 2; a machine
with no C compiler is `ERROR`, never a pass. `--selftest` is fatal and works by
ablation: it rebuilds the harness against a scratch copy of `runtime_native.c`
with the Dict arm stripped and FAILs if the harness still passes, so a harness
that has lost its discriminating power cannot green the guard. If the arm's
source text moves, the selftest reports `ERROR` rather than silently skipping.
