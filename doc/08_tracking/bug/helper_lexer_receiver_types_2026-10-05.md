# Helper lexer projected receiver types

Status: OPEN; source workaround prepared, native checks UNRUN.
Parent failure group: `phase2_subsystem_helper_mir_failures_2026-10-05`.

The six subsystem generator builds using producer `2b831559` report unresolved
CoreLexer `char_at_pos`, `char_slice`, indentation methods, a non-array loop,
text `byte_at`, and optional HashMap `get`/`insert` receivers. Their relocated
MIR positions often point to module globals rather than the original call.
Evidence: `runtime/windows-restart-20261004/six-products-current-proven-transport1/helper-build-failures.json`.

The source already declares `[CoreLexer]`, `[text]`, `[i64]`, and `HashMap?`
owners. This bounded workaround spells those exact types on values extracted
from slots, fields, or optional branches. Every receiver remains evaluated once;
mutable CoreLexer values still write back to the same slot. No receiver-name
fallback, representation cast, dropped validation, or alternate collection is
introduced. Decimal conversion calls the existing `string_to_int` owner used by
the text operation, preserving signed conversion and empty-value fallback; the
older permissive digits-only snapshot helper is not substituted.

The standalone `native_helper_lexer_typed_receivers.spl` has 18 authored checks
for slot calls, UTF-8 indexing, snapshot replay, mutation writeback, byte matching,
signed/empty environment conversion, and HashMap allocation/reuse/owner/reset.
These are source assertions, not executed results. Run with the current compiler
in the repaired helper source overlay, both backends; preserve all failures and
RSS/timing receipts. No active P3/P4 source or cache was changed.

Retirement: verify the equivalent inferred-local fixture with a producer that
retains declaration types through projected and optional values on both backends,
then remove the temporary annotations only if runtime, memory and performance
comparisons show unchanged behavior. The underlying compiler cause remains open.
