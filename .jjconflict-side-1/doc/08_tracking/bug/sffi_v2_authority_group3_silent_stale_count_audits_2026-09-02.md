# sffi-v2-authority group 3: five audits failed silently on stale hardcoded counts

Date: 2026-09-02
Status: FIXED (this change)
Gate: `scripts/check/check-sffi-v2-authority.shs` (blocking push gate,
`push-sffi-v2-authority`). While RED every push in this repo used `--no-verify`,
bypassing all 19 push gates.

## Symptom

Five of the 18 failing guards exited **1 with zero output**. All five were
`set -eu` scripts whose assertions were bare `test`/`[ ]`/`grep -q`, so the
first failure aborted the script before its single trailing `echo ... PASS`.
A guard that fails with no output is why this sat RED unnoticed.

## Failing assertion and classification (all five: LEGITIMATE DRIFT, no breach)

| audit | failing assertion | classification |
|---|---|---|
| `rt-time-contract.shs` | `test 4 -eq 3` on `grep -c 'unsafe(capabilities: [ffi]):' src/lib/nogc_sync_mut/io/time_ops.spl` | The 4th occurrence is `time_now_seconds()` (line 92) wrapping `rt_time_now_seconds()` — the **legacy C integer ABI this same audit already pins** (`int64_t rt_time_now_seconds(void)` in `src/runtime/runtime.c`). Its extern carries `@unsafe(reason: "raw wall-clock second provider", capabilities: [ffi])`. Whole-second clock, no negative-sentinel contract, correctly excluded from the sentinel loop. Legitimate. |
| `io-sffi-authority.shs` | `[ 36 -eq 34 ]` externs (and 38/36 inline, 29/28 blocks, 19/18 facades) | Two externs landed since the audit's baseline `1b4edca296c`: `rt_file_read_text` and `rt_path_basename`. Both arrived with a full `@unsafe(reason: ..., capabilities: [ffi])` annotation plus an `@always_inline` wrapper; `file_read_text_nilable` lexically scopes its raw call. Provider buckets 26/2/6 -> 28/2/6 (both new symbols have native+interpreter providers). Legitimate. |
| `log-sffi-authority.shs` | `test 2 -eq 3` raw externs | `rt_env_get` extern was **removed**; the logger now reads env through the owned facade `std.nogc_sync_mut.env.variables.env_get`. Raw surface shrank 3->2 and scoped raw calls 6->2. This is an SFFI-authority *improvement*; the old expectation would have forced a raw extern back in. |
| `mono-cache-sffi-authority.shs` | `test 0 -eq 3` `extern fn rt_file_` | Module migrated entirely onto `std.nogc_sync_mut.sffi.io.{file_read_text, file_exists, file_write_text}`. Zero raw FFI remains. Same shape as above. |
| `mono-hot-reload-sffi-authority.shs` | `test 0 -eq 4` `extern fn rt_file_` | Migrated onto `std.nogc_sync_mut.sffi.io.{file_exists, file_read_text, file_write_text, file_copy}`. Zero raw FFI remains. |

No hardcoded number was bumped without reading the new occurrence. For the three
facade migrations the expectation was **not** relaxed to the new count — it was
tightened to the strictly stronger invariant (`raw externs == 0`,
`raw call sites == 0`), so re-admitting a raw extern in the mono layer or the
logger now fails.

## Fix

1. Expectations corrected per the table above.
2. Identity pinning, not bare counts: `rt-time-contract` additionally asserts
   the seconds provider's exact `@unsafe(reason:...)` string and wrapper
   signature; `io-sffi-authority` asserts *every* extern is preceded by an
   `@unsafe(...capabilities: [ffi])` annotation, so an unannotated declaration
   cannot hide inside a total.
3. **Silent failure removed (required).** All five now use an inline verdict
   harness and print a verdict LAST on stdout per `.claude/rules/vcs.md`:
   `PASS — <n> assertion(s) checked` / `FAIL — <k> of <n> assertion(s) failed:
   <what, expected vs actual>` / `ERROR — nothing was checked`, exits 0/1/2.
   Non-vacuity is absolute: a missing audited file is ERROR, never a pass, and
   the zero-raw-extern audits carry positive assertions (facade import,
   landmark functions) so a gutted module cannot pass vacuously.
4. `set -e` deliberately dropped (`set -u` kept): `grep -c` exits 1 on zero
   matches, and under `-e` that is exactly what killed these guards silently.
   Exit statuses are read into a variable on the line after the command, never
   through a pipe.

## Proof

Mutation-tested — each guard must go RED on an injected defect:

| injected defect | verdict |
|---|---|
| raw `extern fn rt_file_delete` appended to `cache.spl` | `FAIL — 3 of 10 ... raw rt_* externs (expected 0, actual 1); ...` rc=1 |
| `negative sentinel is failure` stripped from a `time_ops.spl` extern | `FAIL — 1 of 48 ... rt_time_now_unix_micros extern declares negative sentinel is failure` rc=1 |
| `log.spl` removed | `ERROR — nothing was checked (missing .../log.spl)` rc=2 |
| unannotated `extern fn rt_file_bogus` appended to `io.spl` | `FAIL — 3 of 16 ... externs missing an @unsafe(capabilities: [ffi]) annotation (expected 0, actual 1); ...` rc=1 |
| facade import removed from `hot_reload.spl` | `FAIL — 1 of 9 ... owned io facade imported` rc=1 |

Before (all five): exit 1, **no output at all**.
After (unpiped exit status 0 each):

```
I/O SFFI authority audit: PASS — 16 assertion(s) checked (36 declarations; 29 lexical owners; 19 unsafe ambiguous/raw-handle facades; 28 both/2 one/6 no-provider; direct paths mandatory-inline)
Logger SFFI authority: PASS — 10 assertion(s) checked (raw_declarations=2 lexical_raw_calls=2 env=owned-facade disabled_log_fast_path=unchanged)
rt time contract: PASS — 48 assertion(s) checked
Mono cache SFFI authority: PASS — 10 assertion(s) checked (raw_declarations=0 raw_call_sites=0 disk_io=owned-facade O1_memory_hot_path=preserved artifact_admission=absent)
Mono hot-reload SFFI authority: PASS — 9 assertion(s) checked (raw_declarations=0 raw_call_sites=0 disk_io=owned-facade result_error_lifts=present artifact_admission=absent)
```

Parent gate: `sffi-v2-authority: FAIL — 18 of 46` -> `FAIL — 13 of 46`.
The remaining 13 are other groups' audits, being fixed concurrently.

## Flagged, not fixed (out of scope — no source change made)

- `src/lib/nogc_sync_mut/sffi/io.spl`: `extern fn rt_file_read_text(path: text) -> text`
  whose `@unsafe` reason says "nil means read failure", but the return type is
  `text`, not `text?`. The annotation and the signature disagree.
- `src/compiler/40.mono/monomorphize/cache.spl:15` does
  `file_read_text(path) ?? ""` against that non-nilable-typed facade.

Both are annotation/type-representation smells in the audited source, recorded
here rather than laundered into a blessed baseline. They need a separate change.
