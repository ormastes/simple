# Compiled checker per-file transient ownership

- **Id:** `compiled_checker_multifile_rss_retention_2026-08-03`
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  process-persistent strings remain tracked separately as
  `compiled_checker_transient_string_retention_2026-08-03`
- **Severity:** P1
- **Owner:** `src/app/check/main.spl::check_one`

## Symptom and root cause

The compiled checker parsed every command-line file in one process without the
transient lifecycle used by the compiler driver. Parser-created arrays, dicts,
enums, closures, floats, and raw `rt_alloc` allocations consequently remained
registered after each file. A paired Stage 4 cycle2 sample showed near-additive
retention: the median 64-file batch RSS was 1.01 times the sum of isolated
per-file RSS above the 5.25 MiB process base.

`check_one` also returned early for SSpec guidance and error paths, so adding
cleanup to only the success path would have preserved the leak and made later
files order-dependent.

## Fix

Every existing file now enters a per-file transient scope before file read,
guidance, parse, and lint. All post-begin outcomes converge on one cleanup path:

1. `lexer_release_parse_source_globals()` drops lexer/source roots.
2. `rt_transient_array_scope_end()` reclaims file-owned transient objects.
3. `ast_reset()` recreates reusable process-lifetime arena state only after the
   scope has ended.

Scope begin/end failures fail closed. Missing-file, diagnostic ordering,
summary, JSON behavior, and exit status are otherwise unchanged.

The teardown order is load-bearing. Resetting the AST before ending the scope
would allocate the next file's arena inside the dying scope; this is prohibited
by `ast_arena_reset_inside_transient_scope_2026-08-01`.

## Regression coverage

`test/01_unit/app/check/check_multifile_transient_scope_spec.spl` covers:

- a valid file returning success;
- a parser failure;
- SSpec command-block guidance failure;
- a malformed file followed by a valid file in the same process.

The focused interpreter run passed 4/4 examples once.

## Fresh native checker measurement

A fresh x86_64 checker build compiled 46 modules with 0 failures in 22.2 s.
One bounded prefix set used the same 64 real tooling files as cycle2 batch 1;
isolated baseline inputs ranged from 34,048 to 313,076 KiB RSS.

| files | exit | wall | max RSS KiB |
|---:|---:|---:|---:|
| 1 | 1 | 0.11 s | 34,048 |
| 8 | 1 | 1.04 s | 290,224 |
| 32 | 1 | 3.05 s | 716,344 |
| 64 | 1 | 8.78 s | 2,144,728 |

The 64-file stdout and stderr SHA-256 digests exactly matched the pre-fix
cycle2 batch (`0dd8cd…` and empty `e3b0c4…`), and the exit code remained 1.
The prior max RSS was 2,219,888 KiB, so this narrow lifecycle fix reduced the
sample by 75,160 KiB (3.4%). The measured residual slope was 33,503 KiB/file
(32.7 MiB/file).

## Residual retention (not fixed here)

`runtime_native.c::rt_core_reclaim_transient_immortal` deliberately skips
strings, while `rt_string_new_uncached` allocates and registers every string as
process-persistent. Parser token text and derived diagnostic/path strings
therefore dominate the remaining slope even after non-string transient objects
are reclaimed. Fixing string ownership safely is a runtime-wide lifetime change,
not a checker-only cleanup, and is intentionally outside this pure-Simple lane.
It remains open under `compiled_checker_transient_string_retention_2026-08-03`.

## 2026-08-17 verification — runtime lane (classified by CONTENT, not SHA)

**Verdict on the residual item only: ALREADY-FIXED in source.**

The "Residual retention (not fixed here)" section above states that
`runtime_native.c::rt_core_reclaim_transient_immortal` *"deliberately skips
strings"*. That is no longer true of current source. At
`src/runtime/runtime_native.c:1527`, the function's `switch` now has an explicit
string arm ahead of the scope-id arms:

```c
case RT_VALUE_HEAP_STRING: {
    RtCoreString* string = (RtCoreString*)ptr;
    reclaim_string =
        (string->reserved & RT_CORE_STRING_FLAG_TRANSIENT) != 0 &&
        (string->reserved & RT_CORE_STRING_FLAG_SHARED) == 0;
    break;
}
```

and the guard `if (!reclaim_string && (!object_scope || *object_scope != scope_id)) continue;`
lets a transient, non-shared string through to the erase/free path. Strings that
must outlive the scope are excluded by `RT_CORE_STRING_FLAG_SHARED`, which
interned literals set at `:2511`.

**What was NOT proven.** No RSS re-measurement was taken — the 32.7 MiB/file
residual slope quoted above has not been re-run, so the *magnitude* of the
remaining retention is unknown. The prose claim ("skips strings") is refuted by
source; the perf number is simply stale and unverified. The sibling doc
`compiled_checker_transient_string_retention_2026-08-03` should be re-measured
before either is closed.

## 2026-08-17 independent re-verification (second runtime lane)

The 2026-08-17 note above was re-checked against current source and is
**accurate**: `rt_core_reclaim_transient_immortal` is at
`src/runtime/runtime_native.c:1527`, the `case RT_VALUE_HEAP_STRING` arm and its
`RT_CORE_STRING_FLAG_TRANSIENT && !RT_CORE_STRING_FLAG_SHARED` predicate are
present as quoted, and the guard
`if (!reclaim_string && (!object_scope || *object_scope != scope_id)) continue;`
does let a transient non-shared string reach the erase/free path. So the doc's
"Residual retention (not fixed here)" prose — *"deliberately skips strings"* — is
indeed refuted by source.

Its refusal to close is likewise upheld: the doc's claim is a **perf** claim
(33,503 KiB/file residual slope) and no RSS re-measurement was taken by either
lane. A code-shape refutation cannot close a measured-magnitude row. The sibling
`compiled_checker_transient_string_retention_2026-08-03` must be re-measured
first. Status stays OPEN (P3).
