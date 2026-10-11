# Parser pool codec guard batching

The codec-completeness guard now batches source files into each extraction pass
and evaluates all pool encoding/decoding/ownership predicates in one AWK process.
This removes process creation and repeated shell copies per pool. File boundaries
explicitly reset extraction state; a new selftest rejects a synthetic alias or
reset/assignment body split across two files.

Verification on 2026-10-10, baseline release `5646a90e73ec`:

- Eight adversarial selftest fixtures: PASS under Windows Git Bash.
- POSIX shell syntax: PASS.
- Same source, original versus batched guard under Ubuntu WSL: 23.964 s versus
  10.511 s (2.28x faster). Exit status and output match byte for byte.
- Both full scans intentionally retain the existing failure: 178 pools checked;
  `par_initialization_generation_v1` and `par_list_type_import_seen` are reported
  as not encoded/not decoded. This performance change neither suppresses nor
  repairs those baseline findings.
- Windows full scan against the separate item7 source tree completed in
  70.637 s. This is not a matched speedup measurement and not a feature PASS.

The comparison used Python subprocess return codes and retained output, avoiding
ambiguous exit-status capture across PowerShell/WSL shell quoting. Local raw
measurements are in `build/codec-guard-perf-evidence/comparison.json`.
No compiler/runtime source or release artifacts changed in this performance fix.
