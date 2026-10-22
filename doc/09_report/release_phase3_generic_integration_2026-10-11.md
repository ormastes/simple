# release_phase3 generic integration inventory

Original target base: `0c7bb72f83663c4407e694af1388109be25d7ac3` (`origin/release_phase3`).
Work branch: `work/rel-phase3-generics-integrated-20261011`.
Source integration head before refreshed inventory: `60c2eaf388709ca4d723f29f01c535ead0f7ec02`. Previous frozen candidate `ae2b2f13f792` was not built; bootstrap owner explicitly released its source hold for this reviewed repair.
The separate release/1.0 successor at `80485d40aed` remains preserved.

Each commit below was applied individually, then its scope, conflict state and
working status were inspected before the next commit. Clean source transports
were checked against their reviewed patch IDs. This is a source candidate,
not Phase 3, native execution, or full-generics acceptance evidence.

| Original source | Target transport | Scope |
| --- | --- | --- |
| 8dc82bbdf81 | cb459d36265 | Slow completed RSS observations in monitor mode |
| 6cd1f04b1d3 | 5be9f3e8fb1 | Reduced generic proofs in default Lean build |
| dd9e32895a1 | 0c3f5b99c8d | Structural MType substitution proofs |
| 114a3cdacdc | 8b7dac17079 | Restricted native adapter prerequisite |
| f8366dcfb8e, two files only | 23b3381884f | Selection module and its contract test |
| cc9f2a63118 | 053b7924de3 | Adapter execution evidence preservation |
| 73eabe616fd | 8e315e7c5a0 | Producer/backend/runtime receipt binding |
| 8d674f46045 | a30ff1838e2 | Declared copy-propagation helper calls |
| 4ad3d42dd49 | ec7d24d2d17 | Source-root resolution; target call-site adaptation |
| 401bcec747f | b2047401d4e | Reject stripped package-facade fallback |
| 55702478d85, six files only | 2d6d3c65f57 | Cached interpolation optional-list prerequisite |
| 0e0287094ba | f4633420fd9 | Runtime-pair to native-tuple conversion |
| 63ad10caab9 | 0528751d9b5 | Tuple record/container provenance |
| 1c0f01137c4 | 9279908c782 | Ordinary tuple indexed-record provenance |
| 0c36cd05ce1 | a2019db485d | Fixture trailing-blank cleanup |
| 9514acf4b70 | ea0d0141b80 | Generic annotation preservation |
| a0e8e0a56ad | 1bf5d73fca3 | Owner-qualified nominal specialization identity |
| 3037c33b116 | 465a5d9a057 | HIR nominal type relocation |
| 1960bbfaf33 | f96e3feb69c | Cross-table specialization integration |
| 5d07f32c212 | 170861f51d9 | Caller-owned MIR return signatures |
| 72ace788a6f | 226cc8bec3b | Framed model specialization keys |
| d521be9af3e | 6d639d63201 | Imported enum/trait arguments and diagnostics |
| a0f2eddcb25 | 7546665e9fe | Generator carrier guard and wrapper bridges |
| 8a2e9c97b3d | 4b0e8ef0cd6 | AST assembly-kind validation bridge |
| 87cfafde571 | 4816ab4c376 | TryCatch and TypeTest typed traversal |
| d1b0d602d13 | bf6d5f1cd23 | Lambda-local collection and scope isolation |
| 17e3b19ec89 | d79c836b6a1 | Typed optional payload binding |
| 8ed48e9a392 | fa0cf1e022d | Explicit whole-native-build timeout forwarding |
| 61d53aa756ff | 96105b66905 | Symbolic optional binding provenance; symmetric effect guard |
| c05c7204ed3 | 9dd5186ba51 | Newly landed target Windows contract harness fixes |
| 2adf22a2fb2 | 6b690035900 | Stage3 reviewed-repair intent; identity binding unchanged |
| 9fab87545c3 | 60c2eaf3887 | Windows Git capture dialect forwarding and strict receipt schema |

## Overlap and conflict decisions

- Target advanced to `ae9f45d465fdfa772bbcc5c9b4ce833b1b58b9c2` (PR #3064). Its sole substantive commit `c05c7204ed3` was individually applied with identical patch ID; no merge or blanket rebase was used.
- Local target commit `a7eea68a563` was already semantically present: its
  cherry-pick was empty and skipped after inspection. No duplicate commit.
- Keep target `19d98c49928`, `83d8a5ac7cb` and `0c7bb72f836` repairs. The
  Result Err ownership helper, transient state and MIR verifier were not
  replaced with later release/1.0 versions. No files were deleted.
- Resolver conflict: adapt the target's existing call/import to the new
  `from_v1` signature plus `closure_dir`. Preserve the target's already-loaded
  skip; do not import later loaded-owner machinery or undefined helpers.
  Independently reviewed by the integration owner.
- Two documentation append conflicts retained both the formal proof evidence
  and implementation candidate notes.
- Native adapter requires `BootstrapProductSelection`; only its module and
  test were extracted from `f8366dcfb8e`. The broader subsystem SCV changes
  and unrelated native-batch utility `280fb2732ba` are excluded.
- Only cached interpolation changes, their spec, fixture and report were
  extracted from `55702478d85`; unrelated driver/provider changes are excluded.

## Evidence and remaining qualification

At target `a30ff1838e2`, `native-adapter-evidence-test.pl` passed all 24 tests
under MSYS Perl. `product-spec-selection-test.pl` passed all 19 under WSL
Ubuntu Perl. The initial MSYS invocation failed the genuine-symlink negative
because MSYS emulated a copy; strict native symlink creation then failed with
permission denied. Windows symlink behavior is not claimed verified. Neither
passing suite was rerun. Later commits leave these tested files unchanged.

Range whitespace checks passed. Source comparisons confirm the monomorphization
integration, annotation lowering and nominal-key files match reviewed
`17e3b19ec89` before the final reviewed provenance patch. The final monomorphization integration matches `61d53aa756ff`. No Simple executable regression was run on this candidate.

The reviewed-repair shell policy regression passed in its owning lane. Stage4 and unknown reasons are rejected; receipt identity validation is unchanged. Its typed Simple spec and actual standalone planner receipt generation remain UNRUN and required. The final optional producer fixture expects `text=ab int=5 absent=none ordinary=z`; both symmetric and asymmetric effect-bearing provenance negatives remain UNRUN.

Before merge to `release_phase3`, require actual Phase 3 PASS and a compiled,
runnable Hello World from the same frozen source lineage. Also execute the
record/tuple/generic fixtures and focused specs; preserve failures as blockers.
Regenerate fold outputs into an isolated directory with an admitted runtime
and compare all four fold artifacts: five generated bridge lines were manually
synchronized pending that check. Existing Lean passes concern substitution
models only, not full production refinement or model-key encoder injectivity.

Windows progress telemetry still misses orphaned native descendants in the
older live bootstrap. Separate read-only job membership evidence established
that its producer remained in the enforcing Job Object; telemetry omission
does not imply missing job enforcement. No live workload was stopped or altered.

## Reviewed admission repair before successor launch

Old bootstrap evidence demonstrated hermetic preflight discarded the Windows materialization authority, producing a plain Git receipt later compared with a Windows alias receipt. The new repair forwards that authority only to preflight, validates both exact schemas through already tool-bound Perl, and preserves byte-exact before/after checks. Counts, digests, canonical paths, byte lengths, ordering and duplicate rows are validated. Native case identity remains the materialization consumer responsibility. The controlled contract passed under WSL; root independently reviewed with no demonstrated P0/P1. No live receipt was rewritten and no old build was restarted. Windows candidate qualification remains pending. The separate sanitizer reporting fix PR #3068 is intentionally excluded from this frozen compiler candidate.
