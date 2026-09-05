# Silent-Failure Taxonomy — why green builds lie, measured

**Date:** 2026-09-01
**Scope:** the WIDER class around missing-symbol tolerance: every mechanism by
which this tree reports success while being wrong. Missing symbols specifically
are covered by `doc/02_requirements/feature/missing_symbol_early_detection.md`
and
`doc/01_research/compiler/why_missing_symbols_do_not_fail_the_build_2026-09-01.md`
(mechanism analysis, landed by the sibling lane) — this document does not duplicate them.

## 0. The class is the dominant recorded failure mode

Name-matched lower bound over the bug tracker (methodology: filename grep, so
this UNDERCOUNTS — a silent-failure bug whose filename lacks these words is
invisible to it, and the list includes one retraction,
`zero_example_false_green_RETRACTED_2026-07-28.md`):

```sh
ls doc/08_tracking/bug/ | wc -l                                   # 3321
ls doc/08_tracking/bug/ | grep -icE \
  "false_green|silent|vacuous|greenwash|noop|wrong_value|swallow" # 131
```

**131 of 3,321 bug-record filenames (~3.9%) name this class explicitly**, and
the same defect keeps recurring in the same components: the test runner alone
has `test_runner_60s_silent_kill_greenwash_2026-07-04`,
`test_runner_explicit_empty_selection_false_green_2026-07-24`,
`test_runner_emits_no_result_summary_silent_exit0_2026-08-17`, and now the
`outcome=`-ignored fix `206052d53bc` (2026-09-01). Loud breakage gets fixed
once; silent breakage gets re-fixed per instance because nothing prevents the
*pattern*.

## 1. Taxonomy

The working hypothesis was four patterns: (i) vacuous success, (ii) discarded
evidence, (iii) ambiguous sentinel, (iv) tolerated absence. The evidence
**confirms (ii) and (iii), splits (i) in two, and extends (iv)** — because the
hypothesis as stated cannot classify the "silent wrong values" instances at all
(`rt_str_hash` × 3, `use m.{f}` picking another module's `f`): those checks and
lookups inspected something real and still answered wrong. Five root patterns:

### P1. Vacuous verdict — pass with zero evidence examined

The check ran, examined nothing, and reported PASS.

- `check-no-unresolved-runtime-symbols.shs` GREEN on Linux with no artifact to
  inspect, while Windows had 68 unresolved (verified: the guard's own doc in
  `.claude/rules/vcs.md` records exactly this fix history).
- Six specs reporting `executed=0` after a parse crash in `matrix_receipt.spl`
  (session-reported 2026-08-31/09-01; no dedicated bug record located —
  nearest prior art `silently_dropped_spec_examples_2026-08-04.md`,
  `test_runner_explicit_empty_selection_false_green_2026-07-24.md`).
- CBOR `cbor_bytes_are_valid([])` passing vacuously over a slice that was empty
  *because decoding failed* (fixed `afba47bac04`) — chained onto P4 below.

### P2. Non-entailing oracle — evidence examined, predicate does not discriminate

The refinement the four-bucket hypothesis missed. The check inspected real
evidence, but its predicate is a proxy that is also true in failure states.

- Test runner trusted the parsed assertion tally and never read `outcome=`: a
  spec whose assertions passed and which then hit a runtime error reported
  PASS/rc=0 (fixed `206052d53bc`).
- `_is_pending` used `contains` where every sibling used statement-position
  matching, so a COMMENT mentioning the keyword classified a file as a pending
  scaffold — self-demonstrating on its own source (fixed `79ed95e7eb3`).
- `--version` answering cleanly treated as binary health, while both real
  commands SEGV (`check-stage-binaries-runnable.shs` incident 2026-08-18).
- The broad class of guards described in `.claude/rules/vcs.md`: trees that are
  well-formed as BYTES pass every text-and-tree guard while being nonsense to a
  compiler (`runtime_native.c` never-compiled incident 2026-08-11).

### P3. Discarded evidence — the diagnostic path destroys the diagnostic

The failure IS detected; the information needed to act on it is dropped by the
reporting machinery itself. All verified in-session:

- Stage 2 sanity gate hashed the frontend-smoke log into its evidence file then
  `rm -f`'d it: `frontend_status=1` with zero error text, ever (fixed `a927aac3dc3`).
- `head -c 65536` dumped the FIRST 64 KB of a failed build log — all warnings,
  never the error at the end (fixed `a53e5c2f2ba`, now `tail`). **The same
  defect is still LIVE at
  `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:65`**
  (`head -c 65536 "$probe_dir/build.log" >&2` on the failure path — verified
  2026-09-01 by reading the file). 33 `head -c` sites exist under `scripts/`
  (`grep -rn "head -c" scripts/ --include="*.shs"`); most are benign
  previews, but every failure-path one is this bug.
- clang-cl (like `cl.exe`) writes diagnostics to STDOUT; the error path
  captured stderr only, printing `"Failed to compile main stub (clang-cl): "`
  and nothing after the colon (fixed `c4f9781509c`).
- `native_build_main.spl` stderr spill claims "413555 bytes saved" while 211505
  land — the fatal error is emitted LAST and is exactly what is truncated
  (filed: `doc/08_tracking/bug/native_build_stderr_spill_drops_fatal_error_2026-09-01.md`).
  Note it *reports a byte count it never verified* — P3 compounded by P2.
- `_format_mir_error` promised "file:line:col when known" but discarded
  `err.span` (fixed `6298e03514f`); and `body.span` was `(0,0)` on the MIR
  for-in path, so the fix alone still yielded location-blind errors (fixed
  `7adbf53d618`). Two stacked instances on one path.

### P4. Ambiguous sentinel — failure collapses into a legitimate value

The error return is a value the caller cannot distinguish from success:
`[]`, `0`, `nil`, `""`, or a silently truncated result.

- `bytes_slice` returning `[]` on an invalid byte, indistinguishable from a
  legitimate empty slice (fixed `afba47bac04`).
- `rt_string_to_int` truncating at 63 bytes: 62 zeros + `42` returns **4**
  (`rt_string_to_int_silent_truncation_63_bytes_2026-08-31.md`).
- The extern-returns-nil design itself
  (`unregistered_extern_silent_nil_2026-08-01.md`) is this pattern at the
  language level: "not implemented" and "returned nil" are the same value.

### P5. Tolerated multiplicity/absence of definitions — name resolution never requires exactly one

The user's (iv) "tolerated absence", extended: the same root — resolution never
asserts *exactly-one* definition — produces silent wrongness in BOTH
directions. Zero definitions → nil / NULL GOT slot (the missing-symbol class,
mechanism in the sibling doc). MORE than one → an arbitrary winner:

- `rt_str_hash` has THREE live implementations (verified 2026-09-01): correct
  FNV (`src/runtime/runtime_legacy_core.c:243` `spl_str_hash`), a
  truncated-basis FNV
  (`rt_str_hash_truncated_fnv_offset_basis_bootstrap_lane_2026-08-31.md`), and
  djb2 in the Rust seed
  (`src/compiler_rust/runtime/src/value/collections.rs:4562`, `5381u64`;
  `rt_str_hash_rust_seed_djb2_divergence_2026-09-01.md`). Same call, three
  answers, decided by which lane linked. No parity check compares them.
- Explicit `use m.{f}` executing a different module's same-named `f`, decided
  by registration order
  (`tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md`;
  partially fixed upstream).
- Struct passed as a non-`self` argument losing mutations in the caller —
  SEGV under `run`, silently wrong under `test`
  (`bytebuffer_struct_param_mutation_not_persisted_2026-09-01.md`): two engines,
  one semantics question, divergent answers, no cross-engine oracle.
- Link tolerance sites: **21 occurrences across 14 files** of
  `unresolved-symbols=ignore` / `FORCE:UNRESOLVED` / `allow-undefined`
  (grep over `src/ scripts/`, `.spl/.shs/.rs`). Which of these are load-bearing
  is the sibling doc's question; the count is the exposure surface.

## 2. Prevalence — the un-bitten backlog

All commands run at the working tree, 2026-09-01. Re-run them before re-citing;
this tree moves fast.

### 2.1 Vacuous-capable check scripts (P1)

```sh
ls scripts/check/*.shs | wc -l                                     # 795
grep -lE '"?PASS' scripts/check/*.shs | wc -l                      # 503 print PASS
grep -lE "nothing was checked|EV_CHECKED" scripts/check/*.shs | wc -l  # 285 carry the convention
```

**219 scripts print PASS with no trace of the non-vacuity convention** (set
difference of the two lists). That set includes `build-*.shs` builders that are
not verdict guards, so it is an upper bound for the guard population. Narrowing
to scripts that (a) iterate a DISCOVERED list (`find` / `git ls-files` / glob),
(b) print PASS, and (c) contain no zero-count guard and no `ERROR` text at all
— i.e. an empty discovery falls through to PASS — leaves **29 confirmed
vacuous-capable scripts**:

```
scripts/check/build-macos-gpu-2d-live-native.shs
scripts/check/check-arm64-target-runtime-symbols.shs
scripts/check/check-cache-identity-formal-proofs.shs
scripts/check/check-jit-runtime-symbol-manifest.shs
scripts/check/check-llm-caret-claude-cli-trace.shs
scripts/check/check-llm-caret-full-parity-plan.shs
scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs
scripts/check/check-llm-tooling-public-absence-rendering.shs
scripts/check/check-module-surface-hint-scan-fast-path.shs
scripts/check/check-nvme-firmware-remaining-gates.shs
scripts/check/check-nvme-rv32-minimal-live.shs
scripts/check/check-renderdoc-vulkan-capture.shs
scripts/check/check-repo-hygiene.shs
scripts/check/check-riscv-fpga-simpleos-preflight.shs
scripts/check/check-riscv64-fpga-simpleos-preflight.shs
scripts/check/check-rv32-nvme-nand-recovery.shs
scripts/check/check-simpleos-arm64-servers-qemu.shs
scripts/check/check-simpleos-compiler-language-formal-proofs.shs
scripts/check/check-simpleos-formal-coverage.shs
scripts/check/check-simpleos-host-configuration-matrix.shs
scripts/check/check-simpleos-virtio-snd-qemu.shs
scripts/check/check-simpleos-x86_64-crt0-args.shs
scripts/check/check-sosix-positioned-live-route.shs
scripts/check/check-ui-cli-live-transport.shs
scripts/check/check-window-winit-leak.shs
scripts/check/check-x25519mlkem768-metal-ntt.shs
scripts/check/check-x86-32-cpl3-lifecycle-contract.shs
scripts/check/codex-run-guard.shs
scripts/check/produce-aetheric-host-web-gui-evidence.shs
```

(Heuristic, textual: a script in this list may still be safe because its inputs
are hardcoded; a script NOT in it may still be vacuous-capable via a mechanism
the grep cannot see. It is a triage list, not a proof.)

### 2.2 Ambiguous sentinels in the stdlib (P4)

Methodology: count sentinel `return` lines, then narrow to those whose 2
preceding lines contain an error-ish word
(`catch|error|fail|invalid|missing|not found|cannot|bad `):

| sentinel | total in `src/lib` | error-adjacent |
|---|---|---|
| `return []` | 837 | 32 |
| `return nil` | 1,652 | 73 |
| `return ""` | 1,390 | 64 |
| `return 0` (line-end) | 1,242 | 52 |
| **total** | **5,121** | **221** |

**~221 stdlib sites return a legitimate-looking value from an error-adjacent
branch** — each a latent `bytes_slice`/`rt_string_to_int`. The filter is
crude in both directions (a `return nil` after `# not found` may be the
documented contract; a sentinel with no nearby comment is missed), so treat 221
as the order of magnitude, not the roll call. `src/compiler` was not counted;
expect a comparable population.

### 2.3 Discarded-evidence sites (P3)

- 33 `head -c` sites under `scripts/`; **1 verified live failure-path instance**
  (`candidate_frontend_admission.shs:65`), vs 8 `tail -c` sites.
- 10 `rm -f *.log` sites under `scripts/` (each a candidate for the
  `a927aac3dc3` pattern; not individually triaged).
- stderr-only capture of compilers that write diagnostics to stdout: no clean
  grep exists (the pattern is semantic); known instances are the fixed
  `c4f9781509c` and the filed stderr-spill bug. No prevalence number claimed.

### 2.4 Definition multiplicity (P5)

No automated census exists for "runtime symbol with >1 divergent
implementation" — that absence is itself the finding. `rt_str_hash` was found
by a Windows crash, not by any check. The extern-backing census
(`extern-backing-census.shs`) classifies zero-definition symbols only; nothing
classifies N>1.

## 3. Existing countermeasures, and why they still missed

The repo's non-vacuity convention (`PASS — <n> item(s) checked`, `n==0` ⇒
ERROR, `--selftest` fatal — `.claude/rules/vcs.md`) is real and strong **where
applied**: 285 of 795 check scripts carry it. Three gaps let the measured
instances through:

1. **Coverage is opt-in.** The convention lives in prose and in the ~13
   push-tier guards; 219 PASS-printing scripts never adopted it. Nothing
   audits new check scripts for it — the convention itself has no ratchet,
   which is exactly the defect class it exists to catch, one level up.
2. **Non-vacuity does not imply entailment (P2 beats it).** A guard can
   honestly report `n=3819 items checked` and still use a predicate that is
   true in failure states (`--version` liveness, assertion tally without
   `outcome=`, bytes-are-well-formed without compiling). The convention pins
   "did you look", not "does looking there decide the question". vcs.md's own
   history shows each promotion (compile the C, execute the binary, link the
   symbols) arriving only after the corresponding incident.
3. **The convention governs verdicts, not diagnostics (P3 is out of its
   scope).** Every P3 instance occurred in a guard/gate that correctly FAILED —
   and then destroyed the evidence. No rule anywhere constrains the failure
   path's reporting quality, so it regresses freely (`head` vs `tail` fixed in
   one gate on 2026-08-31 and still present in its sibling today).

## 4. Prevention proposals, ranked by value/cost

Load-bearing tolerances that any proposal must NOT break: the bootstrap
chicken-and-egg (a stage must build before the artifact its guard wants
exists); genuinely optional weak hooks; platform-gated code; the ~1,466-symbol
unbacked-extern baseline (Stage 2 proved bulk deletion unsafe); and the
documented sentinel contracts in stdlib APIs (`find`-style "nil means absent"
is a legitimate interface, not a bug). Every proposal below is a *ratchet* or
an *additive check* for exactly this reason.

1. **Non-vacuity ratchet over check scripts themselves** (P1; spec:
   `doc/02_requirements/feature/check_script_non_vacuity_ratchet.md`).
   A meta-guard that scans `scripts/check/*.shs`, classifies each
   verdict-emitting script as convention-carrying or not, freezes today's 219
   as a baseline, and fails any push that ADDS a PASS-capable script without a
   non-vacuity assertion — plus a hand-triage lane for the 29 confirmed. Value:
   converts the repo's best idea from prose into enforcement; the class has
   already bitten at least twice (unresolved-symbols guard, empty-selection
   runner). Cost: one script + baseline, the idiom is established, ~1 day.
   **Highest value/cost of the set.**
2. **Diagnostic-tail preservation rule** (P3; spec:
   `doc/02_requirements/feature/diagnostic_tail_preservation.md`). Greppable
   rule + guard: on a failure path, never `head`-truncate captured output
   (tail or both ends), always capture both streams from compiler-class tools,
   never delete a log you just cited, and verify any byte count you report.
   Immediate concrete yield: the live `candidate_frontend_admission.shs:65`
   instance and the stderr-spill bug. Cheap because the sites are few (33+10
   candidates) and textual.
3. **Error-adjacent sentinel lint** (P4). A lint (family of
   `cow_alias_hotpath`: report at authoring time, ratchet at push) flagging
   `return []/nil/""/0` inside a branch whose guard is an error condition,
   when the function could return `Option`/`Result`. Honest ranking: the
   population is large (~221 in lib alone) and the false-positive rate of any
   textual heuristic is material — this needs the lint infrastructure's
   semantic context, and a baseline from day one. High total value, highest
   cost, do third.
4. **Runtime-symbol parity census** (P5). Extend `extern-backing-census.shs`
   from "zero definitions" to "N definitions": for each `rt_*` name defined in
   more than one lane (C runtime, Rust seed, pure-Simple), require either a
   recorded parity fixture (same inputs, same outputs, `rt_str_hash("a")`
   style) or an allowlist entry stating why divergence is intended. Would have
   caught all three hash implementations before any lane linked.
5. **False-green regression fixtures as a rule.** Any bug record matching
   `*false_green*|*silent*|*vacuous*` must land with a fixture that replays
   the false green and asserts the loud failure — the repo already does this
   ad hoc (`--selftest` fixtures replaying incidents); make it the documented
   bar in `.claude/rules/testing.md`. Near-zero cost; prevents the observed
   re-fix-per-instance churn.

Not proposed: removing link tolerance wholesale, deleting unbacked externs, or
making any existing advisory guard blocking while it is honestly RED — all
three would break the bootstrap or block pushes on other people's debt.
