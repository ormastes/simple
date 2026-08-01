# Vacuous-spec census: 905 specs and ~14,500 test cases are disabled behind fake-green placeholders

**Lane PLACEHOLDER1**, run inline by the orchestrator after the subagent was
halted on an API quota. Method is shell counting over `test/01_unit/**` and
`test/unit/**`; every number below is reproducible with the commands recorded
here.

## The pattern

Lane QSK1 needed specs to validate a 31-file rename and found all five of its
"relevant" specs looked like this:

```
describe "Builder Api":
    it "skipped":
        val pending_reason = "pre-existing test failures - functions/imports not available"
        expect(pending_reason.len()).to_be_greater_than(0)

# # Builder API Tests - Fluent Block Building
# use compiler.blocks.builder.{BlockBuilder}
# describe "BlockBuilder - Construction":
#     it "builds an empty block":
# ...470 more commented-out lines
```

The real test file is **commented out wholesale** and replaced by one assertion
that cannot fail — `expect(pending_reason.len()).to_be_greater_than(0)` is true
by construction. The suite reports `1 total, 1 passed, 0 failed` and goes green.

## Counts

| Shape | Count |
|---|---|
| Spec files scanned (`test/01_unit` + `test/unit`) | 16,253 |
| Files containing `pending_reason` | 1,154 (**7.1%**) |
| Files containing `it "skipped"` | 1,141 |
| **Unique specs after mirror-dedup** | **905** |
| Files with commented-out `describe` blocks | 699 |
| **Commented-out `it "..."` test cases** | **14,535** |
| Files with zero `expect` anywhere | 238 |

`test/unit/` is a known 884-file-diverged mirror of `test/01_unit/`, so the
deduped **905 specs / ~14,500 cases** is the honest figure.

By area (deduped): lib 317, compiler 240, app 225, compiler_core 91, std 18,
compiler_shared 8, os/memleak/bugs 6.  **331 of the 905 guard compiler internals.**

## The reasons are hidden failures, not pending features

This is the finding. Distribution of `pending_reason` strings:

| n | reason |
|---|---|
| 459 | `pre-existing test failures - functions/imports not available` |
| 103 | `imports compiler modules - causes OOM via numbered directory resolution` |
| 98 | `assertion failures - runtime behavior differs in interpreter mode` |
| 31 | `function 'tensor_from_data' not found in interpreter runtime` |
| 24 | `method 'randn_1d' not found on 'dict'` |
| 16 | `module 'compiler_shared.diagnostics' not resolvable` |
| 12 | `variable 'indent_level' not found - struct field access or scope issue` |
| 12 | `std.exp.* path unresolvable from nogc_sync_mut/src/` |
| 12 | `function 'tensor_randn' not found in interpreter runtime` |
| 11 each | `Conv2d__create` / `MaxPool2d__create` not found in interpreter runtime |
| 10 | `timeout - module loading exceeds 60s` |

Not one of the top reasons is "this feature isn't built yet." Every one is a
**symptom of a real defect** — and several name defects this repo has already
documented separately: interpreter-vs-native divergence, dict method dispatch,
module-resolution OOM, the 60s timeout.

The repo rule is *"NEVER skip failing tests without approval."* 905 specs were
skipped, and the failure reason was preserved in a string as the only trace.

## Verification attempted

Re-enabled `builder_api_spec.spl` by uncommenting its body into a scratch spec
and running it: `Results: 1 total, 0 passed, 1 failed`. The underlying breakage
is still present, so these are not stale placeholders guarding already-fixed
code. **Caveat, stated because it matters:** the uncomment was a crude `sed`, and
only 1 of the file's many `describe` blocks registered — so this shows the spec
does not trivially pass, not that all 14,535 cases still fail. A rigorous
re-enable pass is a separate lane.

## Why no bulk repair was done

Re-enabling 905 specs would surface an unknown but large number of real failures
at once. That is the honest state of the tree, but flipping it in one change is a
call for the repo owner, not a lane — and this repo explicitly forbids both
skipping failing tests *and* mass-changing test state without approval.

## Recommendation

1. **Stop the bleeding:** treat `pending_reason` as a lint-detectable anti-pattern
   so no new ones land silently.
2. **Re-enable by cluster, not by file.** The 459 + 98 + 103 groups share root
   causes; fixing one defect likely revives dozens of specs at once. Start with
   the 103 OOM-on-numbered-directory-resolution group, which is one bug.
3. **Report the real number.** Any statement of suite health that counts these
   905 as passing is overstated by ~14,500 cases.

---

# Addendum 2026-08-01 — a third vacuity shape: the spec ships a copy of its subject

The census above covers **file-level** vacuity (body commented out behind a
`pending_reason` / `it "skipped"`). A separate lane covers **assertion-level**
vacuity (SPIPE005: bodies that run but assert nothing). Neither detector sees a
third shape, which is the most misleading of the three because the file looks
like a complete, well-organised, fully-green spec:

**Shim vacuity** — the spec contains a *local reimplementation* of the module it
names, and asserts against the copy. Every example runs, every assertion is a
real assertion, the summary is green, and nothing the shipped code does can ever
change the result.

## Worked case (PROVED)

`test/{01_unit,unit}/app/test_runner/args_spec.spl` opened with

    # Tests for test_runner_args.spl:
    #  - parse_mode_str, parse_test_args

and then defined its own 190-line `parse_test_args` plus its own
`TestExecutionMode`/`TestLevel` enums. It imported nothing. Baseline:
`71 total, 71 passed, 0 failed`.

Because the copy was never reconciled with the shipped parser, it had drifted in
six ways — all of which the spec asserted *as correct*:

| assertion in the copy | shipped `test_runner_args.spl` |
|---|---|
| default `format == "default"` | `"text"` |
| field `has_seed` | field is `seed_set` |
| `mode` is `text` | `mode` is `TestExecutionMode` |
| "ignores second positional argument" | both positionals retained in `paths` |
| `--capture-screenshots` / `--screenshots` / `--refresh-screenshots` / `--refresh-gui-image` / `--screenshot-output` set `capture_screenshots`, `refresh_gui_images`, `screenshot_output` | **none of these flags or fields exist**; the validator answers `unknown option: --screenshots` |
| `parse_mode_str` has 3 outcomes | also `Compile` and `Composite(...)`, incl. `interpreter(...)` normalisation |

The multi-path row is the sharpest: this spec pinned, as expected behaviour, the
exact defect that `1cfed202c53` had to fix (`simple test a.spl b.spl` running
only the first path). It stayed green through both the bug and the fix.

## Non-vacuity proof (PROVED)

Three one-line sabotages to the **shipped implementation**
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` — default `timeout`
120→999, `parse_mode_str` losing the `smf`/`loader` arm, and `--tag` discarding
its value — run against four specs in the same tree, same binary, same command:

| spec | under sabotage |
|---|---|
| `args_spec.spl` (rewritten) | 92 total, **5 failed** |
| `config_parser_spec.spl` (rewritten) | 16 total, **3 failed** |
| `args_spec.spl` **as it was at base** | 71 total, 71 passed, **0 failed** |
| `config_parser_spec.spl` **as it was at base** | 9 total, 9 passed, **0 failed** |

An earlier sabotage set (timeout 120→999, `binary` dropped from `parse_mode_str`,
`--fail-fast` neutered) put the rewritten `args_spec` at **6 failures** with the
original still at 71/71. The originals cannot go red because they never load the
file being sabotaged.

Both rewritten specs are green against unmodified source: 92/92 and 16/16.

## Scale of the shape (INFERRED — static, and an upper bound)

Static scan of 18,862 `*_spec.spl` files: **736 files** (376 unique after the
`test/01_unit` ≡ `test/unit` mirror dedup) have **no implementation import** and
define a function whose distinctive name is also defined under `src/`,
totalling **15,366 live examples**. This is an upper bound: some of those local
functions are genuine test helpers that merely share a name (`float_eq`,
`side_effect`). It is not a verdict on any individual file, only a work queue.

Report the three shapes separately — the repairs are unrelated. File-level
vacuity needs its body restored or the file deleted; assertion-level vacuity
needs assertions added; shim vacuity needs the local copy **deleted** and the
subject imported, and it is the only one of the three that will surface real
API drift the moment it is fixed.

## Detector warning

A first pass at the shim-vacuity count returned **3,118** files. The inflation
was a single generic helper name, `check`, which exists both in `std.spec` and
in hundreds of specs. Filtering generic names cut it to 736 — a **4.2×**
correction, the same failure mode that inflated the earlier `expect(`-only
census 4.7×. Any count of this shape must exclude generic helper names and be
reported as an upper bound.

## Engine reach

All results above come from `bin/simple test` on the 154,185,152-byte Rust
bootstrap seed, which runs the tree-walking interpreter. `parse_test_args` is
pure argument handling with no engine-specific behaviour, so the evidence
transfers; but no spec in this batch reaches the JIT or native lanes, and no
claim here should be read as covering them.

---

# Addendum 2026-08-01 (second shim lane) — the 736 is 155, and a FOURTH shape

## Detector re-derivation (PROVED for the counts, INFERRED for the verdict)

The 736 above was reproduced and then tightened. Same corpus (18,704
`*_spec.spl` under `test/`, 13,804 `.spl` under `src/`, `src/**/vendor/**`
excluded), same base rule — *no implementation `use`, and a locally-defined
`fn` whose name is also defined under `src/`*:

| tier | rule added | files | unique | live examples |
|---|---|---|---|---|
| RAW | base rule only | **5,603** | 4,168 | 65,325 |
| FILT | minus generic-name list | **1,204** | 868 | 20,275 |
| TIER-A | + name defined in ≤3 spec files + local body ≥8 lines | **155** | **109** | **3,497** |

Exclusion list used for FILT (~120 names): `check run parse make setup format
main init new create build get set add test verify assert expect helper reset
clear close open read write print log to_text len size count start stop update
find has is_empty contains push pop value name key result output input data next
prev first last item node join split trim escape unescape encode decode hash
equals compare clone copy apply emit render draw dump load save handle process
execute step tick before after teardown fixture stub mock fake sample gen id
path file dir min max abs sum avg sort reverse map filter reduce zip range slice
error warn info debug trace fail pass skip todo note`.

RAW→FILT is a **4.7× correction**, dominated by two names — `verify` (2,813
files) and `check` (1,712), i.e. the prior lane's `check` finding plus a larger
sibling it missed. FILT→TIER-A is a further **7.8×**.

The two extra TIER-A predicates are what separate a *reimplementation of the
subject* from a *test helper that happens to share a name*: a helper is short
and is copy-pasted into hundreds of specs (`double`, `identity`, `multiply`,
`slow_it`, `check_msg`, `find_simple_binary`), whereas a shim is long and
spec-specific. **Corrected working figure: 155 files / 109 unique specs /
3,497 live examples**, still an upper bound. The list is reproducible from the
tiering rule above; it was not committed (scratch tooling).

## Batch 1 — `app/llm_caret/json_helpers` (PROVED)

`test/{01_unit,unit}/app/llm_caret/json_helpers_spec.spl`, subject
`src/app/llm_caret/json_helpers.spl`.

`test/unit/...` carried a **165-line local copy** of the whole module and
imported nothing. Drift, and it is the sharpest kind:

| the copy | the shipped module |
|---|---|
| `extract_json_string/_value/nested` use `json.index_of()` | uses hand-written `json_find`, added *specifically* to route around the seed's `Option<i64>` tag-box defect (`llm_caret_index_of_optioni64_tagbox_2026-07-07.md`) |
| `extract_json_int` uses `int(raw)` | uses `json_parse_int`, a boxing-free replacement added for the same reason |
| `escape_json_text` hand-rolled | delegates to `std.text.escape_json` |
| `jo4`, `jo5`, `jo6`, `json_find`, `json_parse_int` absent | shipped, and had **zero** coverage |

**The copy reintroduced the exact defect the shipped code exists to avoid.**
It was not merely vacuous, it was *red*: baseline `21 total, 16 passed, 5
failed`, all five in "JSON Parsing", e.g. `expected :42 to equal 42` — the
off-by-one that `json_find` was written to prevent. So the repo was carrying
five permanent red examples that told it nothing about the shipped code.

After: `41 total, 40 passed, 1 failed` on both mirrors.

## A FOURTH vacuity shape: name-collision hijack (PROVED)

The `test/01_unit` mirror had **already been de-shimmed** by an earlier pass —
it imports the shipped module and was `21 total, 21 passed, 0 failed`. It is
still **100% vacuous**, and the sabotage table below proves it.

Cause: it also carries `use std.mcp.helpers.{Q, LB, RB, js, jp}`.
`src/lib/nogc_async_mut/mcp/helpers.spl` defines its **own**
`extract_json_string` (→ `extract_json_string_v2`), `extract_json_value`,
`jo1`, `jo2`, `jo3`, `ja` with **identical signatures**. Co-compiling it makes
those definitions win, so every `extract_json_*` call in that spec is served by
a different module than the one it imported. **No collision warning fires** —
the existing `compiler_cross_module_private_symbol_collision` warning only
triggers on *differing* signatures.

Two independent confirmations:
- `simple run` on the identical call returns the correct `say \"hi\"`;
  `simple test` returns `say \` (the `_v2` implementation has no escape
  tracking). Adding `use std.mcp.helpers` to a `simple run` script flips it
  from correct to wrong, with nothing else changed.
- Under the sabotage below, only the **uniquely-named** functions move
  (`json_find` ×3, `json_parse_int` ×1). Every `extract_json_*` example is
  unmoved, because those calls never reach the sabotaged file.

This is a distinct repair from shim vacuity: the import is already correct and
the local copy is already gone, yet the spec cannot observe its subject. Any
"de-shimming" pass that does not check for same-signature name collisions
produces specs that *look* repaired and are not.

`json_helpers_spec.spl` keeps one deliberately **RED** example
(`extracts a string value containing an escaped quote`) pinning this. It was
not weakened; the assertion is the correct behaviour of the imported subject.

## Non-vacuity proof — the base row is the argument (PROVED)

Three one-line sabotages to the shipped implementation
`src/app/llm_caret/json_helpers.spl` — `json_find` returning `i + 1` on match,
`json_parse_int` dropping its sign handling, and `ja` separating with `;` —
same binary, same command (`bin/simple test <spec>`), restored and
`diff`-verified afterwards:

| spec | clean | under sabotage | Δ |
|---|---|---|---|
| `test/unit/.../json_helpers_spec.spl` (rewritten) | 41 total, 1 failed | 41 total, **5 failed** | **+4** |
| `test/unit/.../json_helpers_spec.spl` **as it was at base** (shim) | 21 total, 5 failed | 21 total, 5 failed | **0** |
| `test/01_unit/.../json_helpers_spec.spl` **as it was at base** (de-shimmed, hijacked) | 21 total, 0 failed | 21 total, **0 failed** | **0** |

Row 3 is the new result: an *already-repaired* spec, green, that stays green
through a three-point sabotage of the file it imports.

## Corrections in both directions

- **5 examples newly correct-and-green**: the five "JSON Parsing" examples that
  were red because the *copy* used `index_of`. They now assert real behaviour
  and pass. A "fewer failures now" metric and a "more failures now" metric both
  mis-score this.
- **+20 examples newly load-bearing**: `json_find` (6), `json_parse_int` (6,
  two of them defect pins), `jo4`/`jo5`/`jo6` (3), plus negative-int, missing
  raw value, nested-miss, message round-trip and padding cases.
- **1 example newly RED**: the escaped-quote hijack above — a real defect that
  no previous state of either mirror could express.

## Defects recorded, not absorbed

1. **`std.mcp.helpers.extract_json_string_v2` has no escape handling** — it
   returns at the first `"`, so `say \"hi\"` truncates to `say \`. Pinned by
   the RED example above. `src/lib/nogc_async_mut/mcp/helpers.spl:104`.
2. **Same-signature cross-module hijack is silent** — see above. The warning
   path needs to cover equal signatures, not only differing ones.
3. **`json_parse_int` skips non-digits instead of rejecting** — `"1a2"` → `12`,
   `"abc"` → `0`. Pinned by two positive controls named `PINS DEFECT: …`.
   `src/app/llm_caret/json_helpers.spl:194`.
4. **Comma-separated `match` arms do not parse** — `65 => "A", 66 => "B"` on one
   line gives `Unexpected token: expected pattern, found Comma`; one arm per
   line works. Minimal repro confirmed on `bin/simple run`. This made
   `src/compiler_rust/lib/std/src/tooling/base64_utils.spl` **unloadable in its
   entirety** — a shipped module that has never compiled, which is why nothing
   in the tree imports it and why its spec could only ever have been a mock.
   Normalised to one-arm-per-line in that file (with the reason recorded in
   place, not silently), verified by running the module: `encode_base64("ABC")`
   → `QUJD`. ~20 other `src/` files match a loose comma-arm pattern and were not
   audited — that is a separate sweep.
5. **`char_to_byte`/`byte_to_char` in `base64_utils.spl` cover only A-J, a-e,
   0-2, space and `!`** — every other byte maps to `0`/`"?"`, so `encode_base64`
   is wrong for ordinary text. Recorded as a `TODO(base64-charmap)` at the site.

## Measurement trap: `use std.*` resolves OUTSIDE the project (PROVED)

The deployed seed resolves `use std.tooling.*` to a **baked absolute path**,
`/home/ormastes/dev/pub/.simple-build-36f5e286/src/compiler_rust/lib/std/src/`,
not to the project root. Editing
`<worktree>/src/compiler_rust/lib/std/src/tooling/base64_utils.spl` and
re-running the spec produced a byte-identical error pointing at the foreign
snapshot; the effect reproduces on `bin/simple run` with a two-line script and
survives copying the binary into the worktree.

Consequences, both bad:
- Any spec importing `std.*` from a worktree is asserting against a **foreign,
  possibly stale copy** of the library, so a green result is not evidence about
  the tree you are editing.
- A sabotage-based non-vacuity proof of any `std.*`-imported module is
  **impossible** from a worktree, because the sabotage is never loaded.

`use app.*` and `use std.nogc_*` do resolve from the project root, which is why
Batch 1 was moved to `app/llm_caret`. The `app/tooling` family (base64, url,
time, format, json, markdown utils — ~270 examples, all pure lookup-table
mocks) is a confirmed shim cluster that **cannot be repaired-and-proved until a
binary is deployed whose stdlib root follows the project**. It is left in place
deliberately rather than rewritten unverified.

## Batch 2 — `app/llm_caret/types` (PROVED)

`test/{01_unit,unit}/app/llm_caret/types_spec.spl`, subject
`src/app/llm_caret/types.spl`.

`test/unit/...` was a **349-line shim**: it redefined all five structs
(`Message`, `ChatRequest`, `ChatResponse`, `StreamEvent`, `ProviderConfig`) and
all eighteen constructors/predicates inline under the comment *"Re-define types
inline for test isolation (import compatibility pattern)"*, and imported
nothing. 26 examples, all green, none able to observe the shipped module.

**No drift.** A body-by-body comparison (whitespace-normalised) found 18/18
functions and all five struct field lists byte-equivalent to the shipped file.
This is an important negative result: a shim can be perfectly faithful *today*
and still be totally vacuous, because nothing makes it stay faithful. It is the
counter-example to the assumption that shim vacuity always shows up as drift.
Disposition: replaced, not because it lied, but because it cannot fail.

The `test/01_unit` mirror had already been de-shimmed (14 field-complete
examples) and its assertions strictly subsume all 26 shim examples, so it was
adopted for both mirrors and extended with two sentinel pins
(`temperature == -1.0` exactly, `max_turns == 0` exactly — the shim asserted
only `temperature < 0`). Result: 16 total, 16 passed, 0 failed on both.

Sabotage (`new_system_message` role `system`→`sys`; `new_chat_request`
`temperature` `-1.0`→`0.5`; `new_success_response` `stop_reason`
`end_turn`→`stop`), restored and diff-verified:

| spec | clean | under sabotage | Δ |
|---|---|---|---|
| `types_spec.spl` (rewritten) | 16 total, 0 failed | 16 total, **4 failed** | **+4** |
| `types_spec.spl` **as it was at base** (shim) | 26 total, 0 failed | 26 total, **0 failed** | **0** |

## Located, not yet repaired — `app/llm_caret/config` (PROVED, no fix landed)

`test/unit/app/llm_caret/config_spec.spl` is a shim (local `_apply_config`,
`parse_config_text`, `reset_config`, plus a generic local `check`) and reports
**22 total, 22 passed, 0 failed**. Its `test/01_unit` mirror has already been
de-shimmed and reports **16 total, 9 passed, 7 failed** against the same
shipped `src/app/llm_caret/config.spl`.

The seven failures are one symptom: parsed values never replace the built-in
defaults — `expected gpt-4o to equal gpt-test`, `expected python3 to equal
python3.13`, `expected 100 to equal 50`, `expected "" to equal
compat-test-key`. So the shim is not merely vacuous; it is **holding a green
badge over seven live failures in its own subject**, which the mirror already
shows. Repair needs the config defect root-caused first and is left for a
follow-up rather than absorbed here.

## Engine reach

Same limit as the first addendum, restated because it now matters more: every
number here is `bin/simple test` on the Rust bootstrap seed. Specs cannot reach
the JIT or native lanes from the test runner. The one place engine choice was
varied (`SIMPLE_EXECUTION_MODE=interpret` vs `jit` on the hijack repro) gave the
same wrong answer in both, which is evidence about the hijack, not coverage of
those lanes.
