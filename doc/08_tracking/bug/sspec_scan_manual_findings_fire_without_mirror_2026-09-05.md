# `sspec-maintain scan` charges manual-content rules against a mirror that does not exist (2026-09-05)

## Symptom

`sspec-maintain scan` applies the manual-content rules — `SSDOC-MNT-005`,
`SSDOC-MNT-008`, `SSDOC-EVD-002`, `SSDOC-EVD-003` — even when **no
`doc/06_spec` mirror file exists at all** for the scanned spec. A single
missing mirror is therefore penalised **five** times: `SSDOC-MNT-002` (−25 mnt)
for the absence itself, plus the four content rules (−15/−15/−10/−20 across
evidence and maintainability), even though there is no manual on disk for
those four rules to have inspected. All four cite a finding path
(`doc/06_spec/<mirror>.md`) that is provably absent.

Aggregate score impact measured on the concrete case below: **97 (correct,
per the independent lane) vs 90 (actual `scan` output)** — a **7-point**
aggregate deficit on every mirror-less spec in the tree, purely from this
double-charge. `mnt` alone drops from 75 to 45 (−30 beyond the legitimate
−25), and `evd` drops from 100 to 70 (−30) for no reason connected to the
spec's real content.

## Documented contract this violates

`.claude/skills/spipe.md` line 356 (SCAN row) states the four content rules
apply **"only when a mirror exists"**:

> **SCAN** | `analyze_sspec_pair_text` + `inspect_sspec_lifecycle_links` |
> `simple sspec-maintain scan <spec> [--min-score N]` | **MNT-002** (-25 mnt =
> **-2.5**) when `doc/06_spec/<mirror>.md` is missing/stale; **MNT-009** (-10
> mnt = -1 each) per lifecycle path that does not exist; MNT-005/008, EVD-002/003
> only when a mirror exists

## Reproduction (verified against real `simple` output, 2026-09-05)

Fixture: `test/01_unit/app/sspec_maintain/scorer_loopholes_spec.spl` has NO
mirror:

```
$ ls doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md
ls: doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md: No such file or directory
```

Direct scan via the bootstrap seed:

```
$ /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run \
    src/app/sspec_maintain/main.spl scan \
    test/01_unit/app/sspec_maintain/scorer_loopholes_spec.spl
SSpec documentization score: 90/100
source: 01_unit/app/sspec_maintain/scorer_loopholes_spec.spl
mirror: doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md (stale)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  ...
01_unit/app/sspec_maintain/scorer_loopholes_spec.spl:1:1: warning SSDOC-MNT-002 [maintainability] (-25): mirrored manual is stale
doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
doc/06_spec/01_unit/app/sspec_maintain/scorer_loopholes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, ...
```

Note the found `mirror_state` is reported as **`(stale)`**, not `(missing)`,
even though the file is absent — a symptom of the same root cause (see below).

Independent lane, same spec:

```
$ sh scripts/check/sspec-score-seed-lane.shs test/01_unit/app/sspec_maintain/scorer_loopholes_spec.spl
GATE SCORE 100 raw=100 ... mirror=unchecked
SCAN SCORE 97 raw=97 blockers=0 nar=100 str=100 ora=100 trc=100 evd=100 cov=100 mnt=75 ... mirror=missing
  SSDOC-MNT-002 -25 L1: mirrored manual is missing
```

**Scan-vs-lane disagreement: 97 (lane, `mnt=75`, `evd=100`, mirror correctly
reported `missing`) vs 90 (real `scan` CLI, `mnt=45`, `evd=70`, mirror
mislabeled `stale`).**

## Root cause (pinned, not merely observed)

The analyzer's own contract is correct in isolation:
`src/app/sspec_maintain/analyzer.spl:480-518` (`_report`,
`analyze_sspec_text`, `analyze_sspec_pair_text`) only invokes
`_manual_findings` (which runs the `SSDOC-MNT-004/005/008`,
`SSDOC-EVD-002/003` detectors, `analyzer.spl:449-465`) when `inspect_mirror`
is true, and each of those detectors (`analyzer.spl:395-447`) is itself gated
on `manual: Option<SspecManualFacts>` being `Some(...)` — a `None` correctly
produces no findings beyond `SSDOC-MNT-002` (`_detect_mnt_002`,
`analyzer.spl:374-380`, gated on `mirror_state == "missing" or "stale"`).

The break is in the CLI plumbing that BUILDS the `mirror: Option<text>`
argument before calling `analyze_sspec_pair_text`, in
`src/app/sspec_maintain/main.spl:203-212`:

```
val mirror = file_read(derive_manual_path(spec_path))
...
mirrors.push(mirror)
```

`file_read` (`src/lib/nogc_sync_mut/io/file_ops.spl:108-110`) delegates to
`read_file_text` (`src/lib/nogc_sync_mut/io_runtime.spl:213-216`):

```
pub fn read_file_text(path: text) -> text:
    match file_read_result(path):
        case Ok(content): content
        case Err(_): ""
```

A missing file's `Err` is silently swallowed to `""`. `main.spl` never calls
`file_exists` on the mirror path before this read, so the resulting `text`
(always non-nil, `""` for a missing file) is pushed straight into
`mirrors: [Option<text>]`, where it is implicitly promoted to `Some("")`.
`analyze_sspec_pair_text` therefore never receives `None` for a genuinely
absent mirror through the real CLI path — it always receives `Some(content)`,
where `content` is `""` when the file is missing. Inside `_report`
(`analyzer.spl:486-493`), `Some("")` takes the `Some(content)` branch:
`manual_facts = Some(extract_sspec_manual_facts(...))` is built from the empty
string, `content.contains(source_facts.source_hash)` is false, so
`mirror_state = "stale"` (explaining the `(stale)` label seen above instead of
`(missing)`), and every manual-content detector now sees `Some(facts)` instead
of `None` and fires against sections/steps/evidence that are naturally all
absent from an empty string — because there was never a real manual to
inspect.

## Affected rule IDs

`SSDOC-MNT-005`, `SSDOC-MNT-008`, `SSDOC-EVD-002`, `SSDOC-EVD-003` (falsely
fired). `SSDOC-MNT-002` itself is unaffected and correct (it is meant to fire
on both `missing` and `stale`).

## Score impact

−7 aggregate points on every spec in the tree with no `doc/06_spec` mirror
(measured: 97 correct vs 90 actual on the concrete fixture above); `mnt`
dimension −30 beyond its legitimate −25, `evd` dimension −30 beyond its
legitimate 0.

## Confirming specs (both RED, as required — see below)

- `test/01_unit/app/sspec_maintain/scan_manual_findings_require_mirror_spec.spl`
  — reproduction: asserts `analyze_sspec_pair_text(path, source, None)` (the
  correct API contract) fires only `SSDOC-MNT-002`, and separately asserts the
  exact `Some("")` shape the real CLI's `file_read` produces for a missing
  mirror (`main.spl:204`) must behave identically — it does not.
  **Verdict:** `SPEC FILE VERDICT: ... outcome=ERROR declared>=2 executed=2
  passed=1 failed=1 skipped=0 dropped=0` — the `None` scenario passes, the
  `Some("")` (real CLI shape) scenario fails, naming
  `SSDOC-EVD-002/EVD-003/SSDOC-MNT-005/SSDOC-MNT-008` as unexpectedly present.
- `test/01_unit/app/sspec_maintain/scan_mirror_missing_vs_stale_spec.spl` —
  generalization: probes the adjacent case of a mirror that genuinely EXISTS
  but is current vs the "no mirror" case, showing the analyzer already
  distinguishes `None` (`mirror_state=missing`) from a real current mirror
  (`mirror_state=current`) correctly, but collapses a CLI-shaped `Some("")`
  into the same buggy "stale, inspected" bucket instead of treating it like
  `None`. **Verdict:** `SPEC FILE VERDICT: ... outcome=ERROR declared>=3
  executed=3 passed=2 failed=1 skipped=0 dropped=0` — the `None` and
  `Some(current-mirror)` scenarios pass, the `Some("")` scenario fails, same
  four rule IDs named.

Per `.claude/rules/testing.md`, both specs are left RED: they correctly assert
behaviour the implementation does not yet have. Do not weaken the assertions
or mark them pending.

## Unblock condition

Either (a) `main.spl` gates the mirror read behind `file_exists` and pushes a
real `None` for a missing mirror (fixing the CLI-to-analyzer boundary, no
analyzer change needed), or (b) the analyzer treats an empty-string mirror
content identically to `None` for the purpose of the manual-content detectors
(fixing the analyzer's own tolerance for the `Some("")` shape). Either fix
should turn `mirror_state` back to `missing` (not `stale`) for this case and
make both specs above go GREEN with their assertions unchanged. This bug
record intentionally does NOT implement either fix — a scoring change here
shifts every score in the repo and needs explicit human sign-off (test-runner
gate default min score 80).
