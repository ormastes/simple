# Feature Specification – Diagnostic Tail Preservation

**Requirements:** (proposed — research at
`doc/01_research/compiler/silent_failure_taxonomy_2026-09-01.md`, pattern P3)
**Plan:** (proposed — no plan doc yet)
**Design:** (proposed)
**Status:** Draft

## Feature Description

When a build, gate, or tool FAILS, the developer always sees the error text —
never a truncated warning preamble, an empty capture, or a deleted log —
because failure-path reporting obeys four enforceable rules: keep the tail,
capture both streams, never delete evidence you cited, and never report a byte
count you did not verify.

## Problem this addresses

Every instance below correctly DETECTED failure and then destroyed the
information needed to act on it (all verified 2026-09-01):

| defect | mechanism | status |
|---|---|---|
| Stage 2 sanity gate: `frontend_status=1`, zero error text ever | log hashed into evidence, then `rm -f`'d | fixed `a927aac3dc3` |
| Failed build dumped 64 KB of warnings, never the error | `head -c 65536` keeps the HEAD; compilers emit the fatal error LAST | fixed `a53e5c2f2ba` |
| Same defect, sibling gate, **STILL LIVE** | `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:65` — `head -c 65536 "$probe_dir/build.log" >&2` on the failure path | open |
| `"Failed to compile main stub (clang-cl): "` + nothing | clang-cl, like `cl.exe`, writes diagnostics to STDOUT; only stderr was captured | fixed `c4f9781509c` |
| "413555 bytes saved", 211505 land, fatal error in the missing tail | spill writer never verified what it wrote | filed `native_build_stderr_spill_drops_fatal_error_2026-09-01.md` |
| Every native-build MIR error location-blind | `_format_mir_error` discarded `err.span`; then `body.span` was `(0,0)` on the for-in path | fixed `6298e03514f`, `7adbf53d618` |

Prevalence of the remaining surface: 33 `head -c` sites and 10 `rm -f *.log`
sites under `scripts/` (vs 8 `tail -c`). The `head`-vs-`tail` defect was fixed
in one gate on 2026-08-31 and sits unfixed in its sibling today — nothing
constrains failure-path reporting quality, so it regresses freely.

## The four rules

1. **Tail rule:** truncating captured output on a failure path must keep the
   tail (or both ends), never the head alone.
2. **Both-streams rule:** invoking a compiler-class tool (`cl.exe`, clang-cl,
   clang, link.exe, cargo) must capture stdout AND stderr into the failure
   diagnostic, or merge them (`2>&1`).
3. **Cited-evidence rule:** a log referenced by an emitted verdict, hash, or
   status line must not be deleted in the same run.
4. **Verified-count rule:** a diagnostic that reports a size/count of saved
   evidence must measure the artifact it wrote, not the buffer it intended to
   write.

## Scenarios

### Scenario: A failed build log is truncated head-first

**Given** a script's failure branch contains `head -c 65536 "$log"` with no accompanying tail dump
**When** the developer pushes
**Then** the guard FAILs naming the file:line and the tail rule

### Scenario: The live known instance is repaired

**Given** `candidate_frontend_admission.shs:65` dumps the head of a failed build log
**When** this feature lands
**Then** that site dumps the tail (matching its already-fixed sibling `a53e5c2f2ba`), and the guard's baseline contains zero entries for it

### Scenario: A spill reports what actually landed

**Given** a stderr spill writes N bytes to disk
**When** it prints "N bytes saved"
**Then** N was obtained by stat/wc on the written file, and a shortfall is itself reported as a warning, never silently

### Scenario: Pre-existing sites do not block unrelated pushes

**Given** benign `head -c` preview sites (e.g. an 80-byte one-line PASS note) exist
**When** the guard classifies them
**Then** success-path previews are exempt; only failure-path truncations count, and pre-existing ones are frozen in a baseline

## Acceptance Criteria

- [ ] Guard `scripts/check/check-diagnostic-tail-preservation.shs` scans `scripts/**/*.shs` for failure-path `head -c`/`head -n` on captured logs and `rm -f` of a file the same script cited in a verdict/evidence line; standard verdict convention, `--selftest` fatal (fixtures: head-on-failure-path FAIL; tail-on-failure-path PASS; success-path preview PASS; empty scan ERROR)
- [ ] Baseline + ratchet: existing offenders frozen, NEW ones fail, repaired-but-baselined fail as stale
- [ ] `candidate_frontend_admission.shs:65` is fixed to `tail -c` as part of landing
- [ ] `native_build_stderr_spill_drops_fatal_error_2026-09-01.md` is resolved: the spill verifies its written byte count and reports shortfall loudly
- [ ] The four rules are recorded in `.claude/rules/` (a short section, not a new file) so authoring-time review can cite them
- [ ] The clang-cl/cl.exe both-streams rule is asserted by at least one regression fixture in the native-build error path (a deliberately failing stub compile must produce non-empty diagnostic text on Windows-style stdout-diagnostic compilers)
- [ ] Wired in `config/check/must_check_gates.sdn` with measured cost (<5s expected)

## Out of Scope

- **`.spl` product code.** The guard's textual scan covers shell scripts;
  the compiler-side instances (span discarding, stderr-only capture in
  `.spl`/`.rs`) are pinned by regression fixtures per fix, not by a grep — no
  reliable textual signature exists for them.
- **Unbounded log retention.** Truncation caps are legitimate (the runaway-
  diagnostic gate deliberately caps a two-line fixture's output); the rule
  governs WHICH end survives, not whether to cap.
- **Deleting the log-retention policy's level-gated logs.** This feature is
  about failure-path evidence, not logging levels; `doc/07_guide/infra/logging/log_retention_policy.md` stands.
- **Success-path output shaping.** Previews, summaries, and `head` on PASS
  paths are fine.

## Notes

Second-ranked in the taxonomy's proposals: smaller surface than the sentinel
population (43 candidate sites vs ~221), fully textual, and it retires one
live, already-diagnosed defect on day one.
