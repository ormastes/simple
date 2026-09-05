# Tracking-corpus status audit, 2026-08-02

**Scope:** every `.md` under `doc/08_tracking/` at `f3354f1924a`.
**Method:** anchored counts with `/usr/bin/grep` pinned (`ugrep` is the
interactive default on this machine and was NOT used).

This audit reports numbers and refutations. It deliberately changes **no**
document's status. A bulk edit across ~2,000 files that looks like a chore while
changing semantics is a known failure mode here.

## 1. Census

| Measure | Count |
|---|---|
| `.md` files under `doc/08_tracking/` | **2,050** |
| ...in `bug/` | 1,805 (1,335 with a status line, 73.9%) |
| ...in `feature/` | 209 |
| ...everywhere else | 36 |
| Carrying a status line (broad predicate) | **1,378 (67.2%)** |
| Carrying a status line (bold-only predicate) | **518 (25.2%)** |

Predicates, stated so they can be re-derived or disputed:

- **broad** — a line matching `^[-*[:space:]|]*\**Status\**[[:space:]]*:`
  case-insensitive. Accepts `**Status:**`, `Status:`, `- status:`,
  `**Status**:` and table cells.
- **bold-only** — a line matching `^\*\*Status:\*\*`, case-insensitive.

### The ~26% figure is REFUTED, and its origin is identified

The handed-down figure was "roughly 1,740 documents, about 26% with a status
field". Both halves are wrong, and the second is wrong in an explainable way:

- the corpus is **2,050** `.md`, not ~1,740
- **25.2%** is exactly what the bold-only predicate yields (518/2050). The
  earlier sweep almost certainly counted `**Status:**` and reported it as "has a
  status field", which undercounts by a factor of 2.6 because most bug docs
  write `Status:` unbolded.

Honest figure: **67.2% of the corpus carries a status line (1,378 of 2,050);
73.9% within `bug/`** (1,335 of 1,805).

## 2. The structural finding — the declared source of truth is unused

`doc/08_tracking/README.md` states the tracker is **DB-first**: `bug/bug_db.sdn`
is the source of truth for defects and `bug/recent_bugs.md` is generated output.

Measured against that claim:

| | |
|---|---|
| `bugs_active` rows in `bug/bug_db.sdn` | **8** |
| `bugs` rows | **0** |
| bug `.md` files on disk | **1,805** |

The canonical defect tracker covers roughly **0.4%** of the defect corpus. The
1,805 free-form `.md` files are the de facto tracker, and nothing enforces a
status field or a vocabulary on them. That, not the percentage in §1, is the real
gap: the convention is not missing, it is bypassed.

Status values present in `bugs_active`: `open` (5), `fixed` (2),
`resolved-duplicate` (1), plus 2 rows with an empty status field.

## 3. Vocabulary — measured inconsistency

Same state is spelled many ways. Closed-ish, from the corpus: `fixed`,
`resolved`, `closed`, `implemented`, `source fixed`, `fixed in source`,
`fixed in seed source`, `source fix implemented`, `fixed / landed`, `mitigated`,
`workaround applied`, `verified with bin/simple fix`. Open-ish: `open`,
`blocked`, `postponed`, `partial`, `partially fixed`, `partially resolved`,
`likely`, `anticipated`, `still ...`, `stale`, `open / fail`.

By first token of each file's FIRST status line (1,377 lines parsed): `open`
497, `fixed` 276, `resolved` 166, `source` 105 (i.e. "source fixed" and
variants), `closed` 44, `root` 36 ("root caused"), `partially` 27,
`implemented` 11, `fix` 11, `partial` 9, `likely` 9, `not` 7, `mitigated` 7,
`workaround` 6.

## 4. Mis-statused docs — what was looked for, and what was NOT found

### 4a. Closed but not done — the dangerous class. NOT confirmed.

209 docs carry a closed-ish status line. Shortlisting those that also contain a
contradiction marker (`FALSELY CLOSED`, `reopened`, `NOT FIXED`, `still
broken/fails/open`, `retracted`, `does not match the tree`, `was never
fixed/implemented`) gave **14**.

**The predicate is REFUTED.** Reading the 14 against their structure, the marker
almost always sits under `## Symptom` (the historical failure the doc exists to
record) or under an explicit scope note, with a `## Resolution` / `## Fix` /
`## Verification` section following. Two spot-checks in depth:

- `aes_xts_ieee1619_kat_mismatch_2026-05-27.md` — "still fails most vectors" is
  line 10, under `## Symptom`; `## Resolution` follows. **Correctly Resolved.**
- `cuda_backend_mirop_signature_field_semantic_false_positive_2026-07-29.md` —
  "Not fixed as part of lane CUDA1" is under `## Scope note`; a later
  `## Root cause (found by lane SIGF)` plus `### Fix` and `### Verification`
  follow. **Correctly FIXED.**

Several others in the 14 (`cranelift_f32_trig_wrapper_codegen`,
`electron_stub_apis`, `interp_for_over_list_generic`) are *honestly scoped* —
status names what was fixed and the doc states the residue plainly. That is good
practice, not a defect. One, `simple_core_pure_simple_archive_builder.md`, is a
pure predicate false positive: its status literally reads `REOPENED`, matched
only because the same line contains "source fixed".

**Conclusion: no confirmed "closed but not done" document was found, and text
contradiction cannot find one.** The closed docs sampled are more disciplined
than the premise assumed. Finding this class for real needs per-doc execution of
the doc's own repro against the current tree — roughly 209 independent
verifications, several of which need a bootstrap. That is a lane, not a sweep,
and it is not claimed here.

### 4b. Open but done. Attempted by tree measurement, signal too noisy to act on.

140 docs carry an open-ish status line. Cross-referencing every `src/`, `test/`
or `scripts/` path they cite against `git ls-tree` at the tip gave 18 docs citing
32 paths that do not exist — a candidate "the work moved on" signal.

**Also unreliable.** Docs routinely cite the **logical** module path rather than
the physical one: `src/compiler/hir/hir_lowering/_Items/declaration_lowering.spl`
does not exist, but `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`
does — the numbered-layer prefix is dropped in prose. At least 4 of the 32 are
this notation difference outright; the rest mix genuine deletions with renames
and Rust-side moves and cannot be separated without opening each one.

The 18-doc shortlist is recorded here as a starting point for a lane that can
afford per-doc verification. It is **not** a list of docs known to be wrong.

## 5. Convention — one exists; do not invent a second

`doc/08_tracking/README.md` already defines the convention: five DB-backed kinds,
`.sdn` as source of truth, generated `.md` for review, and a Feature Done Gate
requiring linked pipeline artifacts before `status=done`. **Follow it.** The
right correction is to land bug records into `bug_db.sdn` rather than to
formalise the free-form `.md` header.

### PROPOSAL (not a ratified convention)

For the ~1,805 narrative bug `.md` that will keep existing alongside the DB, the
minimum viable header is one line, first-token-parseable, using the vocabulary
`bugs_active` already uses so that no third vocabulary is created:

    Status: open | fixed | resolved-duplicate — <free text>

with everything after the em dash unconstrained, so scoped statements
("fixed on the seed JIT lane; pure-Simple pending") stay expressible. Marked as a
**proposal**: it is not in the README today and this audit did not ratify it.

## 6. What this audit changed

Nothing but itself. No document's status was edited. The two classes worth
editing could not be confirmed by any measurement affordable here, and guessing
at 2,050 files is the failure mode this file exists to avoid.

## 7. Verification limits

No bootstrap was run. Counts are `git ls-tree` and pinned-`grep` measurements
over the tree at `f3354f1924a` and are reproducible from the predicates in §1.
The two in-depth doc verifications in §4a are structural readings of those docs
against their own section layout, not executions of their repros — stated as
such rather than claimed as PROVED-by-execution.
