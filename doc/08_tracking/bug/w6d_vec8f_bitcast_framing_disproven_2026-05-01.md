# W6-D / W7-D framing disproven: stage 4 failure is HIR type-inference, not Vec8f.to_array bitcast

**Date:** 2026-05-01
**Status:** FRAMING DISPROVEN — no Vec8f.to_array codegen verifier error exists; the
real stage 4 blocker is a pre-existing HIR type-inference issue already documented in
`aes128_gcm_stub_2026-05-01.md:24`.
**Scoreboard:** 15 of 33+ Wave-N framings disproven (+1 vs prior 14/33 at session start).
**Reference rules:** `feedback_bug_doc_fixes_are_guesses.md`, `feedback_no_coverups.md`.

## Claim under audit (from W6-D / Wave-7 handoff)

> "stage4 codegen verifier error (Vec8f.to_array 32→64 bitcast in SIMD code, not
> interpreter). Blocks `bin/simple build bootstrap --deploy`."

## Empirical repro

```
scripts/bootstrap/bootstrap-from-scratch.sh --deploy   # 2026-05-01 ~06:33Z
```

- Backend selected: `cranelift` (LLVM 18 not installed locally; wrapper falls back).
- Stage 2: PASS — 21963 KB binary, 3.4s.
- Stage 3: PASS — 21963 KB binary, 3.7s, "Stage 3 succeeded".
- Stage 4: **FAIL** — `Build failed: native-build aborted: 66 file(s) failed while
  building explicit entry src/app/cli/main.spl`.
- Output: `build/bootstrap/full/x86_64-unknown-linux-gnu/` is empty (no stage 4 binary).
- Wrapper exit code: 0 (script doesn't propagate stage 4 failure to its own exit — a
  separate latent issue, not in scope here).

Stage 4 build log: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
(124 KB, 132 occurrences of `Cannot infer field type`).

## Actual error pattern

132 errors emitted by the seed Rust HIR lowering pass:

```
src/compiler_rust/compiler/src/hir/lower/error.rs:43:
  #[error("Cannot infer field type: struct '{struct_name}' field '{field}'")]
```

Top breakdown (`uniq -c` on extracted struct/field):

| count | struct | field |
|------:|--------|-------|
| 6 | `Token` | `span` |
| 6 | `Symbol` | `name` |
| 6 | `ANY` | `Unit` |
| 6 | `ANY` | `id` |
| 6 | `ANY` | `exit_code` |
| 4 | `ANY` | `value` / `NoOpt` / `functions` / `Bool` |
| 2 | `wildcard` | `lexer` / `level` / `dim_solver` |
| 2 | `Array {...}` | `length` |
| ... | various concrete structs (`OsTarget`, `HirBlock`, `NLLError`, `CallArg`, ...) | various fields |

First three failing files (representative):

```
src/app/cli/arch_check.spl     hir: Cannot infer field type: struct 'ANY' field 'exit_code'
src/app/cli/cli_helpers.spl    hir: Cannot infer field type: struct 'ANY' field 'exit_code'
src/app/cli/main.spl           hir: Cannot infer field type: struct 'OsTarget'  field 'arch'
```

## What the framing predicted vs what actually happens

| Framing claim | Empirical |
|---|---|
| "codegen verifier error" | False — no codegen runs; HIR fails first. |
| "32→64 bitcast" | False — zero `bitcast`/`verifier` markers in stage 4 log. |
| "Vec8f.to_array" | False — zero `Vec8f` / `to_array` markers in stage 4 log. |
| "in SIMD code" | False — first failures are `app/cli/*` and HIR-layer types, not SIMD. |
| "not interpreter" | True — but irrelevant; the real failure is also not codegen. |

`grep -i 'verifier\|bitcast\|Vec8f\|to_array\|simd' stage4-native-build.log` returns
**zero matches** in the actual error region.

## Why the framing was confidently wrong

W6-D / W7-D appears to have inferred the cause from "this session shipped W6-A AES-NI
(simd_aes_ops.rs) and W5-C Vec16u8" + an assumption that a bitcast verifier issue must
be involved. None of:

- `Vec8f.to_array` is referenced in any spec/test/runtime path that stage 4 traverses
  (it exists only in `src/lib/nogc_sync_mut/simd.spl:158` as a struct method).
- Any bug doc, sstack log, or build crash log references this exact error string.

This matches the `feedback_bug_doc_fixes_are_guesses.md` pattern: a "Proposed Fix"
hypothesis hardened into a "framing" passed across handoffs. It is also the
`feedback_subagent_final_message_glitch.md` pattern: a sub-agent declares a root
cause from an unverified guess, the orchestrator passes it on as fact.

## Pre-existing nature

`doc/08_tracking/bug/aes128_gcm_stub_2026-05-01.md:24` (filed 2026-05-01, BEFORE the
W6/W7 wave) explicitly says:

> Bootstrap rebuilt via `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
> (stages 2–3 verification passed; **stage 4 full-CLI failure is a pre-existing,
> unrelated HIR type-inference issue not caused by this change**).

`doc/08_tracking/bug/engine_2d_limitations.md:79` records the same stage-4 path is
unstable enough that even a self-hosted `bin/simple_stage4` segfaults.

So: stage 4 has been broken in this exact way *before* the W7 wave started, *before*
W6-A's AES-NI work, *before* W5-C's Vec16u8 carrier. The "blocking deploy" framing is
real (deploy is blocked), but the *cause* is misdiagnosed.

## Last green stage 4

`build/bootstrap/full/x86_64-unknown-linux-gnu/simple` from 2026-04-30 09:05:30
(121 MB; built when LLVM-18 was available — used `llvm-lib` backend which has a
different HIR path that did not surface these errors). The current local environment
has fallen back to `cranelift` because `/opt/homebrew/opt/llvm@18` is missing on this
Linux host (the wrapper hard-codes the macOS Homebrew path; another latent wrapper
issue).

## Correct next-step (out of scope for this task)

The real stage 4 fix work is:

1. Determine why the seed compiler's HIR layer (Rust) emits "Cannot infer field type:
   struct 'ANY' field 'X'" on plenty of files where the field is a concrete enum
   variant (e.g., `'ANY' field 'Unit'`, `'ANY' field 'I64'` — these are enum-variant
   *constructors*, not struct fields). The HIR field-access lowering is conflating
   variant access with struct-field access.
2. Independently, the bootstrap wrapper's `llvm@18` discovery path needs to handle
   Linux installs (currently only checks Homebrew macOS paths).

Neither is a "Vec8f.to_array bitcast" fix. Neither is in scope for this Wave-7 lane.

## ACs from the original task — outcome

- **AC-1 Repro:** ✅ stage 4 fails — but with HIR type-inference errors, NOT a
  Vec8f.to_array verifier error. Exact text + counts above.
- **AC-2 Fix at root cause:** ✅ NOT FIXED — because the root cause is not what the
  framing claimed; fabricating a Vec8f bitcast change to "fit" the framing would have
  been a cover-up (`feedback_no_coverups.md`).
- **AC-3 deploy passes:** ❌ deploy still blocked, but on the genuine pre-existing
  HIR issue, not on a Vec8f issue.
- **AC-4 SIMD specs unaffected:** ✅ — no SIMD code touched.
- **AC-5 atomic commits:** ✅ — single `doc(...)` commit recording disproven framing
  in lieu of the planned `fix(codegen): ...` commit which would have been false.

## Files referenced in this audit

- `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log` (today's run)
- `src/compiler_rust/compiler/src/hir/lower/error.rs:43` (error emit site)
- `src/lib/nogc_sync_mut/simd.spl:158` (Vec8f.to_array — exists, untouched, not the cause)
- `doc/08_tracking/bug/aes128_gcm_stub_2026-05-01.md:24` (pre-existing acknowledgment)

## Cross-link

When the actual HIR `Cannot infer field type: struct 'ANY' field 'X'` bug is fixed,
mark this note RESOLVED and link the fix commit. Until then, do not file new
"Vec8f.to_array bitcast" hypotheses against stage 4 — that path is empirically clear.
