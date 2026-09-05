# http_server suite enumeration — drift closure + baseline sweep (2026-08-17)

Lane: `.spipe/simple_enterprise_suite` W14-C (enumeration and evidence).
Scope: close the enumeration-drift hole recorded as an OPEN finding in
`.spipe/simple_enterprise_suite/state.md:730-750`, and record a baseline sweep.
This lane edited **no** `src/**` and **no** `test/**` file, and committed nothing.

Host / runner identity (recorded once, per the lane convention):

- `bin/release/aarch64-apple-darwin/simple` — 29,315,096 bytes, mtime
  `Jul 25 14:15:52 2026`, `--version` → `Simple v1.0.0-beta`.
  (`bin/release/aarch64-apple-darwin-macho/simple` is bootstrap-only and has no
  `test` subcommand — not used.)
- Repo `HEAD` at sweep time: `453610b19f`
  (`docs(enterprise): independent aarch64 verification of the 49-spec suite + WC staleness bug`).

---

## 1. Measured spec count and derivation

```
find test -path '*http_server*' -name '*_spec.spl' -not -path 'test/unit/*' | sort
```

**26 canonical http_server spec files**, all under `test/01_unit/`
(13 in `lib/http_server/`, 12 in `lib/nogc_async_mut/http_server/`, 1 in
`lib/nogc_sync_mut/http_server/`). There are no http_server specs under
`test/02_integration/` or `test/03_system/`.

The unfiltered glob returns 39. The extra 13 live under `test/unit/**`, which is
the **legacy duplicate mirror** fenced by
`scripts/check/check-test-tree-divergence.shs` and its baseline
`scripts/check/test_tree_divergence_baseline.txt`. Every one of those 13 has a
`test/01_unit/**` counterpart, so none is unique content:

| mirror state | count | files |
|---|---|---|
| identical to canonical | 4 | `worker_static_file`, `security_context_dispatch`, `nogc_async_mut/.../static_file_range_parse`, `nogc_async_mut/.../static_file_etag` |
| **diverged** from canonical | 9 | `security_headers`, `csrf`, `rate_limit`, `request_validation`, `nogc_async_mut/.../compression`, `static_file_compression_cache`, `static_file_handler_compression`, `static_compression_cache`, `protocol_handler` |

The mirror is therefore excluded from the suite by construction. Divergence is
reported here as **data only** — fixing it belongs to the divergence baseline
owner, not to this lane.

**The recorded "21" is stale.** Measured today, **20** canonical http_server
specs were absent from the recorded suite (26 on disk − 6 named in the list).
I am not reconstructing lane W10-A's arithmetic; the number above is what the
tree contains today and how it was derived. Six of the 26 were added to the tree
on 2026-08-16/17, after the finding was written, which is itself an instance of
the drift being closed here.

---

## 2. Where the recorded suite lives

| What | Location |
|---|---|
| **The authoritative list** (the one the lane's verify commands are copied from) | `doc/00_llm_process/feature_expert/enterprise_suite/skill.md:83-116` — a fenced ```bash block. Static `bin/simple test <path>` lines at **:85-113**; the ERP example tier already used a glob at **:115**. |
| The OPEN drift finding | `.spipe/simple_enterprise_suite/state.md:730-750` |
| The out-of-suite red table (secondary copy of the same finding) | `doc/00_llm_process/feature_expert/enterprise_suite/skill.md:151-176` |

There is **no machine-readable manifest** anywhere: no spec-list file, no
`.sdn`, no runner config. The "suite" was literally a hand-typed markdown code
block, which is exactly why it drifted silently.

---

## 3. Drift-closing mechanism (implemented)

Two halves — discovery first, guard second.

### 3a. Discovery-based enumeration (the actual fix)

`doc/00_llm_process/feature_expert/enterprise_suite/skill.md` — the six
hand-listed http_server lines were replaced with one discovery loop, matching
the precedent already used for the ubs_test tier at :115:

```bash
for s in $(find test -path '*http_server*' -name '*_spec.spl' -not -path 'test/unit/*' | sort); do bin/simple test "$s"; done
```

The suite **is** the glob: any new `*/http_server/*_spec.spl` file is in the
suite the moment it lands, with no human step. This edit touches only the
markdown wiki entry (allowed — not `src/**`, not `test/**`) and is deliberately
minimal, since other sessions edit that file concurrently.

### 3b. Fail-closed guard

New: `scripts/check/check-http-server-suite-enumeration.shs` (`#!/bin/sh`,
`set -u`, styled on `scripts/check/check-enterprise-cross-os.shs`).

Contract:
- Computes the canonical on-disk set (`test/**`, `test/unit/**` excluded). Zero
  found ⇒ `ERROR`, never a pass.
- If the recorded-suite doc carries the exact discovery line (whitespace- and
  quote-normalized), every spec is covered by construction ⇒ `PASS` with
  `n` = the on-disk count.
- Otherwise it falls back to a **literal path diff in both directions** and
  FAILs, naming every spec on disk but not recorded, and every recorded path no
  longer on disk. It deliberately does **not** eval shell out of markdown —
  exact-line-or-literal-diff is the whole parser.
- Like `check-c-runtime-compiles-push.shs`, this gate checks a **tree**
  (`--root DIR`, default the working tree), not a `BASE..NEW` delta: enumeration
  completeness is a property of a tree, and a push that only *adds* a spec file
  would be invisible to a changed-files-only scan.
- `--selftest` runs before every scan and is fatal.

Verdicts, last line of stdout, `n > 0` always:

```
PASS — <n> spec(s) checked, list matches tree      exit 0
FAIL — <details>                                   exit 1
ERROR — nothing was checked (...)                  exit 2
```

**Selftest (4 fixtures, all must hold):** discovery-loop doc ⇒ PASS with the
mirror file ignored; hand list omitting a spec ⇒ FAIL naming it; hand list
naming a deleted spec ⇒ FAIL naming it; empty tree ⇒ ERROR (a vacuous run can
never read as a pass).

**Live output on this tree:**

```
$ sh scripts/check/check-http-server-suite-enumeration.shs
selftest: 4/4 fixtures OK
PASS — 26 spec(s) checked, list matches tree (discovery loop present in
doc/00_llm_process/feature_expert/enterprise_suite/skill.md; every http_server
spec is in the suite by construction)
exit 0
```

**Negative proof (not a fixture — the real doc with the discovery line removed):**

```
selftest: 4/4 fixtures OK
FAIL — 26 spec(s) checked in '<root>', recorded suite ... uses a hand list and
it does not match the tree; 26 on disk but NOT recorded: <all 26 named>;
fix by restoring the discovery loop
exit 1
```

The guard requires **no** change under `src/**` or `test/**` to go green.

---

## 4. Baseline sweep — 26 canonical specs, one per process

`SIMPLE_TIMEOUT_SECONDS=900 bin/release/aarch64-apple-darwin/simple test <spec>`,
strictly sequential (parallel load is what produced the SIGTERM/no-verdict rows
in earlier sweeps). Authoritative verdict = the final `Results:` line. Every one
of the 26 produced a verdict line; **zero no-verdict rows**, so no re-runs were
needed.

**WC vs HEAD column.** Per the coordinator's warning about stale-working-copy
false reds (`doc/08_tracking/bug/shared_working_copy_109k_lines_behind_origin_2026-08-17.md`),
`git status --porcelain` and `git diff --stat HEAD` were run per spec:
**all 26 spec files were byte-identical to `HEAD` at sweep time** — the column is
uniformly `SAME` and is omitted from the table below rather than repeated 26×.
**Caveat that is NOT clean:** six *library* files under test were locally
modified at sweep time — `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/http/{limits,path_security}.spl`
(`+183/-13` on the sync pair alone). The specs matched committed content; part of
the library they exercise did not.

**Tally: 26 files — 21 GREEN / 5 RED. 275 examples executed, 255 passed, 20 failed.**

| # | Spec (`test/01_unit/`) | total/passed/failed | verdict |
|---|---|---|---|
| 1 | `lib/http_server/accept_header_quality_spec` | 2/2/0 | GREEN |
| 2 | `lib/http_server/chunked_body_boundary_spec` | 14/7/7 | **RED** |
| 3 | `lib/http_server/chunked_rejection_spec` | 15/15/0 | GREEN |
| 4 | `lib/http_server/chunked_size_overflow_spec` | 12/4/8 | **RED** |
| 5 | `lib/http_server/csrf_spec` | 24/24/0 | GREEN ✷ |
| 6 | `lib/http_server/parser_limits_spec` | 23/23/0 | GREEN |
| 7 | `lib/http_server/path_safety_spec` | 30/30/0 | GREEN |
| 8 | `lib/http_server/range_numeric_guard_spec` | 3/3/0 | GREEN |
| 9 | `lib/http_server/rate_limit_spec` | 7/6/1 | **RED** ✷ |
| 10 | `lib/http_server/request_validation_spec` | 12/9/3 | **RED** ✷ |
| 11 | `lib/http_server/security_context_dispatch_spec` | 6/6/0 | GREEN |
| 12 | `lib/http_server/security_headers_spec` | 9/9/0 | GREEN ✷ |
| 13 | `lib/http_server/worker_static_file_spec` | 4/4/0 | GREEN |
| 14 | `lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec` | 6/6/0 | GREEN |
| 15 | `lib/nogc_async_mut/http_server/async_parser_limits_spec` | 18/18/0 | GREEN |
| 16 | `lib/nogc_async_mut/http_server/async_path_safety_spec` | 8/8/0 | GREEN |
| 17 | `lib/nogc_async_mut/http_server/compression_spec` | 20/20/0 | GREEN |
| 18 | `lib/nogc_async_mut/http_server/phase_result_headers_spec` | 16/16/0 | GREEN |
| 19 | `lib/nogc_async_mut/http_server/protocol_handler_spec` | 8/7/1 | **RED** |
| 20 | `lib/nogc_async_mut/http_server/range_numeric_guard_spec` | 3/3/0 | GREEN |
| 21 | `lib/nogc_async_mut/http_server/static_compression_cache_spec` | 8/8/0 | GREEN |
| 22 | `lib/nogc_async_mut/http_server/static_file_compression_cache_spec` | 7/7/0 | GREEN |
| 23 | `lib/nogc_async_mut/http_server/static_file_etag_spec` | 6/6/0 | GREEN |
| 24 | `lib/nogc_async_mut/http_server/static_file_handler_compression_spec` | 9/9/0 | GREEN |
| 25 | `lib/nogc_async_mut/http_server/static_file_range_parse_spec` | 2/2/0 | GREEN |
| 26 | `lib/nogc_sync_mut/http_server/range_numeric_guard_spec` | 3/3/0 | GREEN |

✷ = concurrently owned by W14-A / W14-B; **verdict at sweep time only**.

### Classification of every non-green row

| Spec | Class | Evidence |
|---|---|---|
| `chunked_body_boundary_spec` (7 failed) | **binary/toolchain-blocked** | `Error: semantic: function 'common_index_of' not found`. This is the documented pre-existing interpreter defect: `std.http.headers` imports `index_of as common_index_of` and the aliased import is unresolvable on the deployed interpreter. Already recorded in-tree at `src/lib/nogc_async_mut/http_server/parser.spl:29` and in the lane state log. Not a defect in the spec or in this round's code. |
| `chunked_size_overflow_spec` (8 failed) | **binary/toolchain-blocked** | Same `common_index_of` error text, same root. |
| `rate_limit_spec` (1 failed) | **sibling-owned, verdict at sweep time only** | Assertion red with no message surfaced by the runner. File was `== HEAD` at sweep time; W14-A/W14-B are actively editing it. See conflict note below. |
| `request_validation_spec` (3 failed) | **sibling-owned, verdict at sweep time only** | Same shape as above. |
| `protocol_handler_spec` (1 failed) | **code/spec-failed (pre-existing, attributed)** | `Error: semantic: type mismatch: comparing string with integer` — a string-vs-integer mismatch inside the spec's own case. The lane state log recorded this same 7/8 in Wave A and confirmed by import-closure analysis that the file is untouched by the enterprise lane. Unchanged today. |

Neither of the two known Jul-25 binary defects the brief named — `use app.<pkg>.main`
→ "cannot convert dict to int", and typed-`u8` byte-array element — appeared in
any of the 26 logs. The one genuinely toolchain-shaped blocker in this family is
the `common_index_of` alias, above.

### The recorded "9 RED / 168 examples / 37 failed" number is superseded

Re-derived honestly today: **5 red, 275 examples, 20 failed**, over 26 files
rather than 21. The old tally should not be repeated. Three of its rows are
demonstrably no longer true:

- `security_headers_spec` 7/0 with "function `default_security_headers_config`
  not found" → **9/9 GREEN** today.
- `rate_limit_spec` 6/0 with "function `default_rate_limit_config` not found"
  → **7 executed, 6 passed** today (the API-not-found class is gone).
- `request_validation_spec` 11/0 same class → **12 executed, 9 passed** today.

Sibling lane W14-B's finding is consistent with this and explains the original
number: `git log -S default_rate_limit_config -- src/` returns zero commits, so
that free function never existed; the real API is
`RateLimitConfig.default()` / `RateLimitStore.new()` / `rate_limit_handler`, and
the "orphaned against a nonexistent API" reds were measured against a working
copy reverted to pre-fix text.

**Open conflict, stated rather than smoothed over:** W14-B reports
`rate_limit_spec` and `request_validation_spec` **fully green (7/7, 12/12)** at
HEAD, while this sweep — with both spec files verified byte-identical to
`HEAD` `453610b19f` — measured 6/7 and 9/12.

The obvious "dirty library" explanation was **tested and is dead**. Both specs'
import closure is `std.http_server.{rate_limit,request_validation,types}`; a grep
of those three modules for `std.http.limits` / `std.http.path_security` returns
zero hits, and `git status --porcelain -- src/lib/nogc_sync_mut/http_server/`
is **empty** — the whole `http_server` library directory was clean against HEAD
during the sweep. The six modified `src/lib/*/http/{limits,path_security}.spl`
files are not in these specs' dependency path.

That leaves the **runner** as the leading explanation: this sweep ran the Jul-25
aarch64 `bin/release/aarch64-apple-darwin/simple`; W14-B's numbers come from a
different binary (and possibly a different HEAD in a lane worktree). Unresolved.
Whoever closes the triage should re-measure both specs on a single named binary
and single named sha, and say which side moved.

### Why the guard does not also assert WC == HEAD

Considered and deliberately declined. A green sweep over a stale working copy is
a real hazard in this lane, but it is a *different* invariant from enumeration
completeness, and it already has an owner:
`doc/08_tracking/bug/shared_working_copy_109k_lines_behind_origin_2026-08-17.md`
plus the committed-content discipline the pre-push guards already enforce
(`check-test-tree-divergence.shs --ref`, `check-seed-builds-push.shs`). Folding a
cleanliness check into this gate would make it FAIL on every legitimate
mid-edit tree — including right now, while two siblings hold uncommitted spec
edits — which is precisely the fail-open pressure that gets a guard downgraded to
advisory. The correct shape, if wanted, is a separate `--ref <sha>` mode that
enumerates from `git ls-tree` instead of the working copy; that is a
one-function addition to this script and is left as a stated follow-up, not
silently omitted. The **sweep** in §4 carries the WC-vs-HEAD evidence per file
instead, which is where the misleading conclusion actually gets drawn.

---

## 5. Found but deliberately not fixed (needs an owner)

1. **The OPEN finding in `.spipe/simple_enterprise_suite/state.md:730-750` is
   still open in that file.** Its second half ("fold all into the recorded
   suite") is now done, but this lane is forbidden from appending to `state.md`
   (concurrent edit; an append already conflicted once in this lane). Follow-up
   edit, for whoever owns the merge: replace the "Next action" sentence at
   `state.md:746-750` with a pointer to this report and to
   `scripts/check/check-http-server-suite-enumeration.shs`, leaving the triage
   half open under W14-A/W14-B.
2. **The "49/49 spec files GREEN" whole-suite paragraph at
   `doc/00_llm_process/feature_expert/enterprise_suite/skill.md:69-79`** is stale
   for the http_server tier — it sits directly above an enumeration that is
   21/26. A one-line supersession pointer to this report was added inside the
   discovery-loop comment so a reader cannot take the 49/49 at face value, but
   the paragraph itself still needs re-measuring by whoever owns the whole-suite
   number.
3. **The stale red table at
   `doc/00_llm_process/feature_expert/enterprise_suite/skill.md:151-176`** still
   lists the superseded 9-RED / 37-failed numbers and the "function not found"
   causes that no longer reproduce. Not rewritten here to keep this lane's edit
   to that concurrently-held file minimal (one loop, §3a). Follow-up: replace
   that table with §4 of this report.
4. **`common_index_of` alias unresolvable on the deployed interpreter** — the
   single toolchain root behind 15 of the 20 failed examples. Worked around in
   `http_core` already; the alias itself is still broken in
   `std.http.{headers,request}` across three tiers.
5. **9 diverged `test/unit/**` mirror copies** of http_server specs (§1). Owned
   by the test-tree divergence baseline, not by this lane.
6. **Six uncommitted `src/lib/*/http/{limits,path_security}.spl` modifications**
   present in the shared working copy during the sweep. Not touched (forbidden
   and sibling-owned), but they make the library side of this sweep
   non-reproducible from `HEAD` alone.
