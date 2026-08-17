# BUG: 88 shell-out specs target `bin/release/simple`, which currently refuses to run

- **Filed:** 2026-08-17
- **Lane:** batch_00 (CORE + P1 + silently-wrong-results)
- **Severity:** High — systemic false evidence. Not a wrong answer in the
  compiler; a wrong answer in the thing we use to *judge* the compiler.
- **Status:** OPEN — one spec repaired as the proof case, 87 not yet audited.
- **Found via:** `codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`

## Symptom

`test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl` reports

```
SPEC FILE VERDICT: declared>=3 executed=3 passed=0 failed=3 dropped=0
Results: 3 total, 0 passed, 3 failed
```

on a compiler where the defect it guards is **fixed**. Running its own fixture
directly prints exactly the values the spec demands:

```
$ bin/simple run test/01_unit/compiler/codegen/fixtures/erased_receiver_index_of.spl
erased=6
typed=6
user=999
```

## Root cause

The spec resolves its compiler under test to `bin/release/simple`. That path is
**not the compiler** — it is a 2181-byte bash production-guard wrapper, and it
currently refuses the deployed runtime:

```
$ out=$(bin/release/simple run <fixture> 2>&1); rc=$?
TRUE_rc=1
stdout_bytes=122
error: refusing non-production Simple runtime: bin/release/x86_64-unknown-linux-gnu/simple
```

The refusal is correct behaviour on its own terms — the deployed binary is the
Rust seed (`bin/simple`, mtime 2026-08-16 22:59), and the wrapper exists to stop
a seed masquerading as production. The bug is that **88 specs use that wrapper as
their process-under-test**, so the fixture never executes, stdout comes back
empty, and every `assert_true(result.0.contains(...))` fails.

Three assertion failures that all mean "the subprocess never started" are
visually indistinguishable from three that mean "the compiler emitted wrong
code". That is what makes this a silent-wrong-result bug rather than a broken
path: it does not report an error, it reports a **plausible, specific,
compiler-shaped failure**.

## Blast radius

```
$ grep -rln 'bin/release/simple' test/ | wc -l
100
# of those, files that also spawn a process (rt_process_run/spawn/exec/sh -c):
88
```

Spans `01_unit/compiler/{codegen,driver}`, `03_system/feature/{language,usage,
web_platform,parser}`, `03_system/os/simpleos`, `01_unit/os`, `05_perf`. Notably
it includes `test/03_system/feature/language/parent_commit_piped_result_spec.spl`,
which is the spec cited as reproduction evidence by
`cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md` — so at
least one *other* open P1's stated evidence is suspect for this same reason and
must be re-measured before its status is trusted.

Direction of the error matters: this produces **false RED**, not false green. It
does not hide compiler defects; it manufactures phantom ones and burns lanes
chasing them. But a spec that can never pass also can never catch a real
regression, so these 88 are simultaneously not gates.

## Fix applied (1 of 88)

`erased_receiver_index_of_bind_spec.spl`:

1. Default target changed `bin/release/simple` -> `bin/simple` (the documented
   default tool path, which execs whatever is deployed). `SIMPLE_SPEC_COMPILER`
   still overrides.
2. Added a **prevention** example that asserts the subprocess actually ran —
   `rc == 0` and non-empty stdout — *before* any assertion about its content, so
   "did not run" can never again present as "ran wrong". This is the generalizing
   guard: it fails for a bad path, a refusing wrapper, or a missing fixture
   alike, in any spec of this shape.
3. Collapsed three content examples into one. Each `it` costs a full compiler
   subprocess launch; at four launches the run exceeded the test daemon's budget
   and returned `timeout=1 reason=daemon-no-response budget_ms=120000` with **no
   `Results:` line at all** — an inconclusive run that reads like a failing one.

## Remaining work

Audit the other 87. The mechanical part is the path; the important part is that
each one gets the ran-vs-ran-wrong guard, because the path will break again the
next time the deployed binary changes provenance.

## Measurement note (this bug bit its own investigation)

The first reading of the wrapper's exit status was taken through a pipe
(`bin/release/simple ... | head`) and came back `0`, which suggested the wrapper
was succeeding and the compiler was at fault. The pipe returns `head`'s status.
Re-measured with `out=$(cmd); rc=$?` it is `1`. Same trap the project rules
already document; recorded here because it landed on the exact bug it obscures.
