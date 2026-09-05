# Dead-entry-point specs — a third vacuity mechanism

Census date: 2026-08-02. Base: `61e66f5566`.

## The mechanism

Distinct from the two already fixed:

- `fn main` in a spec makes `run` take the JIT entry path and drop every
  module-level `describe`/`it` — fixed in `f93a9abb5d0d`.
- Matcher-less `expect` reported PASS on a falsy subject — fixed in `62c075bbe3cf`.
- **This one:** the file has no top-level `describe` and no `fn main`, so the
  spipe runner discovers **zero** examples. Its tests live inside a top-level
  `fn <name>_test()` that **nothing anywhere invokes**. Running the file exits
  **0** having asserted nothing.

Both other mechanisms concern assertions that run but do not bite. Here the
assertions never execute at all.

## Predicate

A file is DEAD_ENTRY when all hold:

1. under `test/`, `*.spl`
2. no `^describe ` at column 0 (those ARE auto-discovered and do run)
3. no `^fn main`
4. defines at least one entry-shaped top-level fn (`*_test`, `*_tests`,
   `run_*`, `test_*`)
5. no reference to that name anywhere in the repo **that is not itself a
   top-level definition of the same name**

Clause 5's exclusion is load-bearing. Without it the census reported **zero**
dead files, contradicting a case already proved dead by hand: these specs are
duplicated at `test/system/...` and `test/03_system/os/...`, and each copy's
definition was being counted as the other's caller. Any future run of this
census must keep that exclusion.

Tooling note: pin `/usr/bin/grep`; `grep` is ugrep on these dev machines and
differs on `-r`/pattern handling.

## Result

Of 20,002 `test/**/*.spl`: 18,696 have a top-level `describe` (live), 754 have
`fn main` (the separate, already-fixed shape), 510 have neither a describe nor
an entry-shaped fn, 26 are live via a real caller, and **16 are DEAD_ENTRY**.

The 16 are 8 unique files each duplicated at a legacy `test/system/...` path.

### PROVED dead — verified by name AND by path

Zero callers of the entry name, and zero references to the file path outside
`test/` (no harness, no CI job, no OS entry registration). Assertion counts are
`_assert(` call sites in the file — coverage that has never once executed.

| file | entry fn | `_assert` calls |
|---|---|---|
| `test/03_system/os/os_ssh_spec.spl` | `os_ssh_test` | 187 |
| `test/03_system/os/os_shell_spec.spl` | `os_shell_test` | 65 |
| `test/03_system/os/os_full_stack_spec.spl` | `os_full_stack_test` | 24 |
| `test/03_system/os/os_shell_userland_tools_spec.spl` | `os_userland_tools_test` | 23 |
| `test/03_system/os/os_storage_spec.spl` | `os_storage_test` | 21 |
| `test/03_system/os/os_network_spec.spl` | `os_network_test` | 16 |

**336 assertions, none of which have ever run.** `os_ssh_spec.spl` alone
advertises 143 tests in its header comment.

### PROVED dead, no assertions to recover

| file | entry fn | note |
|---|---|---|
| `test/02_integration/compiler/mixin_type_inference.spl` | 5 `test_*` fns | no assertion calls |
| `test/02_integration/t32_hw/t32_hw_helpers.spl` | `t32_hw_build_capi_test` | helper module |

## Correction to the existing vacuity tracker

`vacuous_spec_candidates_2026-08-01.tsv` classifies all six OS specs as
`NOASSERT_INERT` with `n_assert=0`. That is **wrong and it understates the
damage**: `os_ssh_spec.spl` has 187 assertions, not zero. That counter only
recognises spipe-style `expect(`/`assert` and does not see these files' own
`_assert(` harness. "No assertions" implies nothing is lost; the truth is that
336 assertions of real coverage are dark. The `NOASSERT_INERT` class should not
be read as covering this shape.

## Why wiring them up is not a one-line change

Three separate problems beyond the missing caller:

1. `_report()` writes to the QEMU `isa-debug-exit` port. `.claude/rules/board-runnable.md`
   forbids `isa-debug-exit` outright. It also never sets a real process exit
   code, so even when reached the run cannot fail a build.
2. `_assert` only increments a counter and prints. A failure is not fatal.
3. `os_full_stack_spec.spl` never calls `_report()` at all.

So the entry point is dead, and the reporting path behind it would not fail a
build even if it were live.

## Truth reveals — confirmed, not predicted

`os_storage_spec.spl` (smallest, 21 assertions) was wired with a temporary
`fn main` calling its entry. It reached `=== OS Storage Integration Test ===`
and then died:

```
error: semantic: variable `sosix_dataset_active` not found
```

`sosix_dataset_active` IS declared, at `src/os/sosix/share.spl:33`:

```
var sosix_dataset_active: [bool; 64]
```

A module-level `var` with a type annotation and **no initializer**. It is used
at lines 66, 139, 165, 166 and 209 of that same file. This is production
SimpleOS storage code that cannot resolve its own module-level state — invisible
until now precisely because the only spec covering it never ran. Related to the
known module-level-binding registration defect.

The same run also surfaced, in `_vfs_boot_q35_perf_u64_field`:

```
[CODEGEN-AMBIGUOUS-METHOD] bare method 'to_i32' has 6 candidates:
[DivergenceKind.to_i32, DivergenceKind_dot_to_i32, EventKind.to_i32,
 EventKind_dot_to_i32, KernelReplayMode.to_i32, KernelReplayMode_dot_to_i32]
— refusing to pick shortest (would silently miscall)
```

The JIT refused the body and fell back to the interpreter. Failing closed is
correct here; the ambiguity is still a real defect.

The temporary `fn main` was reverted — it is NOT part of this change. Wiring is
deliberately not landed yet: it would turn six specs red on defects this change
did not cause, and the fix belongs with whoever owns `src/os/sosix`. Nothing was
weakened or silenced to avoid that.

## Follow-ups

1. Fix `src/os/sosix/share.spl` module-level `var` registration, then wire
   `os_storage_spec` and confirm its 21 assertions pass.
2. Work the remaining five specs in descending assertion order:
   ssh (187), shell (65), full_stack (24), userland_tools (23), network (16).
3. Replace `isa-debug-exit` in `_report()` with a real non-zero exit, and make
   `_assert` failures fatal, or the newly-live specs still cannot fail a build.
4. De-duplicate the legacy `test/system/...` mirrors — they are what broke the
   first version of this census.
5. `test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` holds the
   ONLY positive RSA-PSS verification assertion in the tree and **times out at
   600 s**, so RSA-PSS has no working positive coverage. The negative-only
   assertions elsewhere cannot distinguish a working verifier from one that
   returns false for everything.
