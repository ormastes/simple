# BUG: 88 shell-out specs target `bin/release/simple`, which currently refuses to run

- **Filed:** 2026-08-17
- **Lane:** batch_00 (CORE + P1 + silently-wrong-results)
- **Severity:** High — systemic false evidence. Not a wrong answer in the
  compiler; a wrong answer in the thing we use to *judge* the compiler.
- **Status:** **FIXED 2026-08-17** — the wrapper-path half was already remediated tree-wide; the residual RED was a *different, deeper* defect (`rt_env_get` returning `nil`), now fixed in the runtime. See "Resolution".
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

## Resolution 2026-08-17

### Part 1 — the "87 unaudited" figure no longer describes the tree

Re-censused today. Of the 104 files under `test/` that still mention
`bin/release/simple`, **none uses it as the process under test any more**:

```
$ grep -rn '"\(\./\)\?bin/release/simple"' <files that also spawn a process>
test/01_unit/compiler/driver/compile_delegation_guard_spec.spl:32
test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl:34,45,53,54
test/unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl:34,45,53,54
```

Every remaining hit is the string passed as **data** to
`is_release_wrapper_self_delegation(...)` — specs whose subject *is* the wrapper
guard. The rest of the 104 are prose: the warning docstring this record's fix
introduced, propagated across the scv / nvme / usage families. So the mechanical
path half is done.

### Part 2 — the proof case was still RED, for a NEW reason, and it was a product bug

The record's own prevention example ("the fixture subprocess actually ran") is
what caught it. Re-run on the 2026-08-17 12:58 seed:

```
$ bin/simple test test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl --no-session-daemon --sequential
✗ produces fixture output rather than failing silently
    runtime: rt_process_run: cmd must be a string
Results: 2 total, 0 passed, 2 failed
```

Not a path problem at all. Minimised to a 6-line probe:

```simple
extern fn rt_env_get(key: text) -> text
val o = rt_env_get("SIMPLE_SPEC_COMPILER_NOPE")   # unset
print("is_nil=" + (o == nil).to_text())    # is_nil=true
print("empty=" + (o == "").to_text())      # empty=false
```

**`rt_env_get` is declared `-> text` in every Simple-side declaration in the
tree, but returned `nil` for an unset variable.** That makes the universal
optional-override idiom take the *wrong* branch —

```simple
val override = rt_env_get("SIMPLE_SPEC_COMPILER")
if override != "":        # nil != "" is TRUE
    return override       # ...so it returns nil
```

— and hands a non-text to whatever consumes it. The same hazard is already
recorded in `src/lib/log.spl:1027` ("unguarded `rt_env_get(...).len()` on a nil
env var"), so this spec was not the only victim, merely the one with a guard
sharp enough to notice.

Fixed in `src/compiler_rust/runtime/src/value/sffi/env_process.rs`: an unset
variable now yields the empty string, matching the declared return type. `NIL`
is retained only for a malformed key pointer, which is a real error rather than
an absent value. Presence is queried with `rt_env_exists`, which is what
distinguishes unset from set-to-empty — so no information is lost.

### Evidence

Fixed binary `/mnt/data/cargo-target-sweep/release/simple` (59570248 bytes,
built from this change; the deployed `bin/simple` is the older 2026-08-17
12:58:51 seed and still shows the defect, which is the A/B):

```
$ /mnt/data/cargo-target-sweep/release/simple test test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl --no-session-daemon --sequential
rc=0
  ✓ produces fixture output rather than failing silently
  ✓ binds every receiver shape to the method its own type owns
SPEC FILE VERDICT: ... declared>=2 executed=2 passed=2 failed=0 dropped=0
Results: 2 total, 2 passed, 0 failed
```

The probe above on the same binary: `is_nil=false`, `empty=true`, and a
previously-fatal `rt_process_run(compiler_bin(), ...)` now runs.

**Deployment caveat, stated rather than glossed:** the fix is in the Rust seed
runtime and is proven on a binary built from this change. `bin/simple` still
points at the older seed, so the spec stays RED there until a redeploy. That is
a deployment step, not an unfixed defect.

Status: FIXED.

## Re-run on rebuilt seed 2026-08-17 (seed md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45)

    bin/simple test test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl --no-session-daemon --sequential
    SPEC FILE VERDICT: ... declared>=2 executed=2 passed=2 failed=0 dropped=0   (exit 0)

GREEN. The canonical repro spec now passes end to end on the rebuilt seed,
consistent with the `rt_env_get` nil fix being live. Only this one spec was
re-run — the other 87 shell-out specs named in this record were NOT re-checked,
so the wider roster claim is not yet re-verified.
