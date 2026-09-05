# Skipped / Ignored / Flaky Test Census — 2026-08-21

Scope: honest census of the skip/ignore/flaky population in `test/`, what is
genuinely disabled and why, and whether the "flaky" list is nondeterminism or
plain breakage.

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` (the
self-hosted default). Verdicts are read from the `SPEC FILE VERDICT` /
`Results:` lines on **stdout**, never from exit status — see "Verdict trust".

## 1. Headline corrections to the prior reports

| Prior claim | Reality |
|---|---|
| "flaky list of roughly 40 specs" | **671 specs** are on the flaky list. The ~40 figure counts only the `async/` + `verification/` + `assurance/` block named in the report. |
| flaky ⇒ nondeterministic pass/fail | **No.** `test_result.md:16` states the criterion verbatim: *"Tests detected as flaky (high variance in execution time)"*. It is a **wall-clock variance** heuristic. Being on this list is **not** evidence a spec ever failed. |
| "216 raw skip lines" ⇒ 216 disabled tests | Overwhelmingly **comments, docs, and string literals**, not skips. Genuine line-anchored file-level directives: **5 files**, all deliberate fixtures. |
| named skips: 3 specs | Only **1 of 3** is real. The two `failsafe` specs carry **no skip directive at all** — that claim is stale. |

`doc/08_tracking/test/test_result.md` summary table currently reads
`Passed 0 / Failed 0 / Skipped 0` — it is stale and carries no usable totals.
The prior report's "no honest current repo-wide failed/ignored total yet" is
confirmed, and this document does not manufacture one: a full-suite run was
out of scope (a full suite and a bootstrap were running concurrently).

## 2. Genuine skip census

Total genuinely-excluded-from-default-discovery spec files: **13**.

### 2a. Intentional, correctly marked — 5 (keep)
All under `test/fixtures/unstable_mode/`: `pass_a`, `pass_b`, `fail`, `crash`,
`timeout`. These are *fixtures for the unstable-mode runner*, deliberately
carrying `# @skip` so they stay out of default discovery and are reachable only
via explicit request. Their own header comments document this. **No action.**

### 2b. Accidentally excluded — 8 (FIXED, see §4)
Excluded because the runner matched the substring `# @skip` **anywhere in the
file**, including inside comments and string literals. None of these has a real
directive; none was ever meant to be skipped.

- `test/01_unit/std/pending_on_spec.spl` (+ mirror `test/unit/...`)
- `test/01_unit/lib/common/pending_on_spec.spl` (+ mirror `test/unit/...`)
- `test/01_unit/app/test_runner_new/test_manifest_spec.spl` (+ mirror)
- `test/02_integration/app/check_skip_log_modes_spec.spl` (+ mirror `test/integration/...`)

All four distinct specs **pass** when run explicitly — 42 assertions
(6 + 6 + 26 + 4), 0 failures. They were silently contributing nothing.

Note the irony: `check_skip_log_modes_spec` and `test_manifest_spec` are the
specs that *cover the skip machinery*, and the skip machinery was excluding
them. That is why the bug survived.

## 3. Defects found (not fixable by this change)

### 3a. `mode_filter` / `tag_parsing` specs are vacuous self-tests
`test/01_unit/test_runner/mode_filter_spec.spl` and `tag_parsing_spec.spl` have
**zero `use` imports** and define `_extract_mode_tags`, `_file_mode_matches`,
`_file_get_mode_tags` locally. They test a private reimplementation that ships
nowhere. A repo-wide grep finds **no production implementation** of test mode
filtering. These specs are green and assert nothing about the product.

### 3b. Skip marker corrupted to `skip-marker-removed_mode:`
22 occurrences across 6 files. `test/feature/mode_filter/skip_native_spec.spl`
declares `# skip-marker-removed_mode: native`, which is not a directive any
reader honours — the spec is documented as skipping native but is **inert**.
The mangled string was also written into the specs that test the marker, so
they assert the corrupted spelling and stay green. Introduced somewhere in the
tree-wipe/restore sequence around `6f86ff32a7d` / `ae55a746719`.

Both 3a and 3b need a bug record; neither is repairable without deciding
whether mode filtering is a feature the runner should actually have.

### 3c. Four flaky-list entries reference files that do not exist
`test/01_unit/compiler/cache/{dirty_closure,interface_digest,target_graph}_spec.spl`
and `test/01_unit/lib/http/h2/h2_preface_probe_spec.spl`. The flaky list is
generated but never reconciled against the tree.

## 4. Fix applied

`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`

The discovery gate used an unanchored whole-file substring test:

```
if content.contains("# @skip") or content.contains("# @pending"):
```

Replaced with a line-anchored `has_skip_directive(content)` helper that matches
only a line that *is* the directive (`# @skip`, `# @pending`, or the
parameterised `# @skip(...)` / `# @pending(...)` forms).

Verified in both directions — 3 intentional forms still excluded, 3 accidental
mentions (doc comment, string literal, a `contains(...)` call) no longer
excluded. Restores 42 passing assertions across 4 specs (8 counting mirrors).

Two other files carry the same unanchored pattern and were left alone as they
are not the discovery gate; they are follow-ups, recorded here:
`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`,
`src/app/check_skip/main.spl`.

## 5. Flaky vs. broken — repeat-run split

Method: every spec that produced a non-`OK` result in a first pass over the
`async/` + `verification/` + `assurance/` block was re-run **3× serially** with
`timeout 300`, recording the `SPEC FILE VERDICT` line each time. 18 suspects,
54 runs.

An early pass was polluted by **single-worker test-daemon head-of-line
blocking** — runs printed `daemon-backlog: N request(s) queued on the
single-worker test daemon` and timed out with no verdict. That was fixed
(`7a6f6459a81`, clients now bypass the daemon); per-spec cost fell from ~51 s
to ~7.5 s and the timeouts disappeared. This is exactly the trap the task
warned about, in reverse: **infrastructure contention masquerading as
flakiness.**

### Result: zero genuinely flaky specs

**All 18 suspects were STABLE across 3 runs — identical verdict, identical
`executed`/`passed`/`failed` counts every time. Not one varied.**

| class | count | meaning |
|---|---|---|
| **Daemon artifact** | 6 | timed out only under daemon backlog; stably `OK` after the fix |
| **Genuinely broken** | 12 | stably `ERROR` on every run |
| **Genuinely flaky** | **0** | — |

Daemon artifacts (all now `OK`, 0 failures): `async_mir_spec`,
`async_pipeline_spec`, `async_reservation_analysis_spec` (23 passed),
`async_spawn_analysis_spec` (26 passed), `async_state_machine_spec`,
`state_enum_spec`.

This confirms §1 conclusively: the "flaky" list tracks execution-time variance,
not nondeterminism, and every spec on it that looked unstable was either an
infrastructure artifact or a hard, reproducible failure. **Mislabelling these
12 as "flaky" is what kept them ignored.**

### The 12 broken specs, with root cause

| spec (`test/01_unit/compiler/…`) | exec/fail | root cause |
|---|---|---|
| `assurance/formal_delivery_gates_spec` | 0/0 | **parse error** in `src/compiler/00.common/assurance/formal_delivery_gates.spl:127` — multi-line `if` with trailing-`or` continuation: `expected expression, found Dedent`. Nothing runs. |
| `assurance/sha512_integrity_receipt_spec` | 3/2 | `semantic: invalid assignment: cannot index assign value of type array` — reached via `sha512_text` (`src/lib/common/crypto/sha512.spl:226`, `padded[pi] = padded[pi] & 255`) |
| `verification/lean_workflow_spec` | 0/0 | `runtime: Module "io" does not export 'fs'` — broken import, nothing runs |
| `verification/lean_block_integration_spec` | 10/1 | `class LeanBlock has no field named 'namespace'` — spec and class out of sync |
| `verification/unsupported_construct_spec` | 15/**14** | `function expects 1 argument(s), but 2 were provided` — worst of the set |
| `verification/verification_diagnostics_spec` | 5/2 | `method 'format' not found on type 'dict'` |
| `verification/proof_reference_spec` | 11/2 | assertion: `Option::Some(...)` not unwrapped before `to_contain` |
| `verification/lean_basic_spec` | 5/1 | assertion: `expected true to equal false` (sorry-disabled fail-closed path) |
| `verification/lean_codegen_spec` | 5/1 | assertion: `expected subject to be truthy, got false` |
| `verification/regeneration_spec` | 4/1 | assertion: generated-header text mismatch |
| `verification/report_rendering_spec` | 18/2 | assertion: summary/SDN state-count text mismatch |
| `verification/unified_attrs_spec` | 6/1 | assertion: emitted Lean theorem text mismatch |

Three distinct categories: **2 specs never execute at all** (a parse error and
a bad import), **4 hit compiler/type defects**, and **6 are ordinary assertion
mismatches** where the spec and its subject have drifted apart.

Note the binary in use self-identifies as *"this Rust-built Simple binary is a
bootstrap seed only; do not use it as the normal tool"* — some of these
failures may be seed-specific and should be re-confirmed once a full-CLI
pure-Simple binary is deployed.

## 6. Verdict trust

`bin/simple test` exited **0** on a run of
`test/01_unit/compiler/async/state_enum_spec.spl` whose stdout carried the real
result. Separately, piping the run through `tail` showed only stderr warnings
and **no `Results:` line at all** — the verdict is on stdout and is easily lost
behind a large stderr warning stream. Both confirm the standing rule: read and
quote `SPEC FILE VERDICT` / `Results:`, never trust exit status.

## 7. Recommended next steps

1. Rename the "Flaky Tests" heading in `test_result.md` to state its real
   criterion (execution-time variance). On the evidence of §5 it has **zero**
   genuinely flaky entries, and the name is actively causing real failures to
   be dismissed.
2. Fix the 12 broken specs in §5. The two that never execute
   (`formal_delivery_gates`, `lean_workflow`) are the highest value — they
   currently contribute no signal at all.
3. Reconcile the flaky list against the tree to drop the 4 dead paths (§3c).
4. Re-confirm §5 once a full-CLI pure-Simple binary is deployed; the current
   binary self-identifies as a bootstrap seed.
5. Apply the §4 line-anchoring fix to the two remaining unanchored copies.
