# Post-HIR ownership admission repeatedly normalizes module paths

Status: ordering repair implemented; isolated native behavior/performance PASS;
full-CLI timeout resolution and SSpec execution pending rebuilt qualification.

## Retained failure

Source `1a1a95a7443766176f64fb5abec27f01807437ee`, Cranelift/AArch64,
Stage-2 producer SHA-256
`bbe7bc6e6303378851effe773f52c1e89a377e370119197086de4c6a189c525f`.
Campaign: `/tmp/phase3-release100-j10-lifecycle-1a1a95a7443-20261024`.
The full CLI HIR warmers completed seven workers with zero failures. The final
native worker adopted 2,911 cached modules and lowered one. It finished the
2,912-module HIR loop at 530,813 ms, then emitted HIR phase completion at
999,925 ms: 469,112 ms in post-loop work. The outer CLI row timed out with
status 124; MIR entry was never observed. The earlier worker attempt timed out
during surface construction. These are separate boundaries; this change does
not claim to repair all closure-loading or post-HIR costs.

Full worker logs are retained under the campaign's
`stage2-compiler-tests/aarch64-unknown-linux-gnu/cache/compiler-tools/stage2/`
producer/runtime directories, `full-cli/diagnostics/native-build-stderr-4083106-{1,2}.log`.

## Concrete defect and repair

`driver_nogc_param_effect_admission_v1` selection-sorted modules by calling
`module_surface_canonical_path` for every remaining module on every selection.
For N=2,912 this performs N(N+1)/2 = 4,241,328 path resolutions and split/join
normalizations, retaining allocation pressure under the native no-GC runtime.

The repair normalizes exactly N keys, then stable-merge-sorts scalar indices
using two N-element buffers. It retains the prior text comparison and original
input order on equal canonical paths. HIR payloads stay in their existing
owner; the sort only addresses them by index. The admission rounds, provider
visibility, conflict checks and transactional publication remain unchanged.
Existing later pairwise membership/publication scans are outside this patch.
Profile-gated ownership-admission start/done/failure markers make the remaining
post-HIR cost attributable on the next qualification.

## Executed native evidence

Evidence root: `build/native_probe/hir-admission-order-20261025/` in the migration
worktree. All three fixture executables were compiled by the producer above
with `SIMPLE_NO_STUB_FALLBACK=1`, Cranelift and one thread. The focused main
printed `hir-admission-order PASS`, exit 0, after empty/single/equal-key/odd-run
and input-preservation checks.

The benchmark uses 2,912 long snapshot-like paths with duplicate keys. Both
implementations receive already-canonical keys: the old normalization cost is
deliberately excluded, so this measures a conservative sorting-only change.
Each execution checks permutation, order and stable ties and prints the same
checksum `893047177`. Five paired executions all exited 0.

| Metric | Previous selection | Candidate merge |
|---|---:|---:|
| elapsed samples (s) | .35, .37, .35, .36, .37 | .01, .01, .00, .01, .01 |
| median elapsed (s) | .36 | .01 |
| observed p95 / maximum (s; five samples) | .37 | .01 |
| maximum RSS (KiB) | 4,012 | 3,692 |

The timer resolution is 0.01 s; `.00` is below resolution, not zero work.
Time ratio is at most .01/.37 = .0271; memory ratio is 3692/4012 = .9203;
their sum is .9474. These numbers establish the isolated sorter only, not a
full compiler time or RSS improvement.

Baseline executable SHA-256:
`eb765ac4fd7e452a598a4e840cd30ad997096dc3720213fd2da959088c5a59cd`.
Candidate executable SHA-256:
`b24546a7e8af151209387e682a748cc11e26966f54eb95aaa5e4a5cb52da6798`.

## Regression and qualification boundary

- `test/01_unit/compiler/driver/hir_admission_order_v1_spec.spl`: empty/single,
  stable equal keys, canonical aliases, odd-sized reversed input and sorted input.
- `driver_nogc_param_effect_gate_spec.spl`: actual post-HIR gate publishes
  unordered shard modules in physical order while retaining module owners.
- `test/fixtures/compiler/hir_admission_order/{main,baseline,candidate}.spl`:
  executed native behavior and paired performance fixtures.

The SSpec suite and optimizer CLI require a usable full CLI, which this campaign
has not produced. They were not executed through the Rust seed. The broader
source repair still requires a rebuilt compiler and full-closure qualification.

The first native fixture used an inferred `expected` integer-array local; this
producer read its element as nil in the comparison. Explicit `[i64]` annotation
restored the expected scalar values. That independent inferred-array typing
gap is not repaired here; its observed reproducer/evidence is the retained
`compile-diagnostic.log` and pre-annotation `index=0 actual=3 expected=` output.
Bug database reconciliation remains pending a qualified full CLI.
