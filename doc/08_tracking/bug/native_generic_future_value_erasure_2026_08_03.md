# Native generic Future value erasure

Status: claimed; monomorphization follow-up required
Severity: P1 native language correctness
Owner: pure-Simple HIR/MIR generic class and enum specialization
Fix owner: unassigned outside the Stage 4 declaration-containment repair
Claimed source revision: uncommitted repair after `69757e3aae7`

## Exact observation

The first focused native containment fixture compiled `Future<i64>` and
`Poll<i64>` successfully with stub fallback disabled, but polling
`Future.from_value(41)` reached `Poll.Ready` with a value other than `41`. The
fixture exited 42 with empty stdout/stderr. This confirms the Phase-A warning:
native generic class/enum erasure can compile and then silently return a wrong
value even when no method-level generic is involved.

The Stage 4 blocker repair must not turn this pre-existing corruption into a
passing behavioral claim. Its positive native regression is therefore limited
to lowering/import containment, while interpreter behavior continues to be
tested normally. Native generic Future behavior remains unsupported until real
specialization is implemented and this exact ready/pending value fixture exits
30.

## Required follow-up

1. Preserve the concrete `T` through `Future<T>` fields, `Poll<T>` payloads,
   static constructors, and `poll()` return lowering.
2. Reject every unsupported native construction/call before codegen; compiling
   a wrong value is never an acceptable fallback.
3. Restore the retained ready/pending executable assertion and require exit 30
   before advertising native `Future<T>` support.

## Retained evidence

- `build/focused/stage4-nogc-async-future/contract-attempt1.log`
- `build/focused/stage4-nogc-async-future/contract-attempt1.stdout`
- `build/focused/stage4-nogc-async-future/contract-attempt1.stderr`

The fresh-session negative `Future.from_value(1).map(increment)` fixture adds a
stronger failure observation without changing this status: the retained
pre-repair Stage 3 compiler accepted it, but its executable segfaulted with
exit 139 and empty output. This is not a native Future behavior PASS and is not
a substitute for real specialization.
