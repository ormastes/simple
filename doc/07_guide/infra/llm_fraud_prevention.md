# LLM Fraud Prevention — `rules.sdl` and the shrink gates

An LLM agent under pressure to show green has three cheap exits: delete the failing
test, shrink the list the checker walks, or skip the lane that would have caught it.
Each one *reduces* something and each one looks like progress in a diff. This layer
makes reduction the one thing that cannot pass silently.

**The invariant, in one line:** counts and lists that represent coverage may grow
freely and may never shrink without a reviewed, recorded, human decision.

## Why a registry and not more guards

The repo already has ~57 pre-push guards. The gap they left is that nothing enumerated
what *must exist* — each guard knew its own invariant, and a guard that stopped being
invoked, or a baseline that quietly got smaller, was invisible. `rules.sdl` is that
enumeration: one declarative file listing the tests, scripts, counts, and lanes the
repo promises to keep. It is itself a count gate, so shrinking the registry to escape
the registry is the first thing blocked.

## What it covers

| Gate kind | Fraud it blocks |
|---|---|
| `count_gates` | Deleting specs, md doctests, comment doctests, or check scripts to make a census pass |
| `file_gates` | A rebase/merge/stale-snapshot silently truncating a referenced guard script |
| `list_gates` | "Fixing" lint by growing an allowlist; hiding clang errors by shortening the list walked |
| `base_files` | Stray root-directory file creation, missing load-bearing files |
| `scenarios` | Skipping the expensive lanes (QEMU boot, FPGA, accel system test) and reporting green |
| self-integrity | Editing `rules.sdl` itself to remove the gate that was about to fail |

## Two groups: quick and full

`quick` is the default — it runs on every pre-push and is cheap enough not to be
routed around. `full` adds the heavy scenario lanes and is what **bootstrap** runs,
plus anyone who asks for it explicitly. The split exists so the fast gate stays fast;
it is not a licence to leave `full` unrun, which is why bootstrap forces it.

```bash
sh scripts/check/check-rules-sdl.shs --group quick     # default, pre-push
sh scripts/check/check-rules-sdl.shs --group full      # bootstrap / on demand
```

## Reading the verdict

Every script here follows the repo convention: the verdict is the **last line of
stdout**, and exit status is corroboration only, never the primary signal.

| verdict | exit | meaning |
|---|---|---|
| `PASS — <n> gates checked, ...` | 0 | safe; `n` is always > 0 |
| `FAIL — ...` | 1 | a gate shrank; do not push |
| `SKIPPED — <LANE> NOT VERIFIED` | 0 | hardware absent; the lane made **no claim** |
| `ERROR — nothing was checked` | 2 | could not determine; do not push |

A run that evaluates zero gates is an `ERROR`, not a pass. This is deliberate: the
most common way a guard fails open in this repo is by checking nothing and exiting 0.

`SKIPPED` exists for the FPGA lane, which needs physical hardware. It exits 0 so it
does not block unrelated work, but it prints an unmistakable notice and the full-group
summary surfaces it — a skipped lane is never counted as a passing one.

## How to legally reduce a gate

Reduction is allowed. Silent reduction is not. The procedure is mechanical so that
"I had a good reason" cannot be asserted after the fact:

1. **Write down why**, as a tombstone line in `rules.sdl` beside the gate:
   `# removed: <reason> <doc/08_tracking/bug/...md>`. The integrity guard fails on a
   removed gate id with no tombstone.
2. **Update the baseline deliberately** with `--generate-baseline`, having read the
   diff. That flag exists for reviewed updates only; running it to clear a red you
   did not investigate is the exact fraud this layer exists to stop.
3. **Record it in the commit message.** A step-over that is not recorded is a
   violation even when the delta is otherwise clean.

## Where enforcement actually happens

Local git hooks are necessary but not sufficient here: **`pre-commit` is not installed
in this clone, and jj bypasses git hooks entirely.** Confirmed by adversarial review
2026-08-11: `jj git push` / the `sj` wrapper around it (`bin/sj` ->
`src/app/sj/main.spl`, a thin jj/git passthrough with no push-specific hook point)
never invokes `.git/hooks/pre-push`, so on the documented landing flow
(`sj bookmark set main -r @- && sj git push --bookmark main`) the quick-group
rules.sdl gates never ran. See
`doc/08_tracking/bug/jj_push_bypasses_rules_sdl_gates_2026-08-11.md`. So the
load-bearing enforcement points are:

- **`sh scripts/check/land.shs`** — the documented landing command
  (`.claude/rules/vcs.md`). Runs `check-rules-sdl.shs --group quick --ref <tip>`
  and `check-rules-sdl-integrity.shs <base> <tip>` against COMMITTED content
  (never the shared working copy), refuses to push on any verdict other than
  `PASS`, and only then runs the actual `sj`/`jj` push. This is now the primary
  enforcement point for the normal (non-bootstrap) landing path — raw
  `sj`/`jj git push` bypasses it entirely and should be treated as unsafe.
- **pre-push** — via `scripts/check/pre-push-conflict-tree-guard.shs`, the aggregator
  that already fans out to the other guards. This only fires on a REAL `git push`,
  which the jj landing flow never performs, so it protects direct `git push` users
  only.
- **bootstrap** — `bin/simple build bootstrap` runs the `full` group, so the expensive
  lanes are proven at the point a compiler is deployed.

Anything relying on `pre-commit` alone should be treated as advisory. Residual risk:
`land.shs` only protects users who run it; a user who runs raw `sj`/`jj git push`
still bypasses every quick-group gate — there is no mechanism that forces that.

## The lanes

| gate | what it proves |
|---|---|
| `spec_files`, `spec_it_cases`, `md_doctest_files`, `comment_doctest_files` | the three test kinds the runner discovers did not shrink |
| `check_scripts`, `rules_sdl_gates` | the guard corpus and this registry did not shrink |
| `pre_push_aggregator`, `tree_size_guard`, `divergence_guard`, `root_workspace_guard` | a rebase/merge did not truncate a load-bearing guard script |
| `root_file_allowlist` | root-dir file creation is still fenced by `FILE.md` |
| `lint_census_classifier`, `clang_error_free` | the lint classifier and the seed build still hold |
| `sspec_pixel_region_ignore` | GUI image compare can mask regions **and** a fully masked comparison still cannot pass |
| `qemu_boot_hello` | SimpleOS boots on real firmware, `ls` works, hello compiles and runs in-guest |
| `fpga_rv_linux` | Linux boots on the Simple RISC-V core and `ls` returns entries |
| `webdb_accel` | the accelerated db scan returns the right rows and does not overclaim SIMD |
| `startup_declared_args` | the pre-main parser accepts only manifest-declared arguments |

Scenario and list lanes report a verdict *line*, so each encodes it as `2` = PASS,
`1` = SKIPPED, `0` = anything else. `min: 1` where hardware may legitimately be absent,
`min: 2` where it may not.

## Adding a gate

Add an entry to `rules.sdl`, run `--generate-baseline`, and commit both. Then prove
the gate bites: break the invariant, confirm the guard goes red, revert, confirm green
again — and report all three observations. A gate that has never been seen to fail is
not known to work.

## See also

- Plan and phasing: `doc/03_plan/infra/llm_fraud_prevention/rules_sdl_anti_fraud_plan.md`
- Expert notes: `doc/00_llm_process/feature_expert/rules_sdl/skill.md`
- Precedents this follows: `scripts/check/check-test-tree-divergence.shs` (baseline +
  scoped delta escape), `scripts/check/check-guard-wiring.shs` (ratchet with a
  mandatory written reason), `config/critical_files.sdn` (per-file shrink thresholds)
