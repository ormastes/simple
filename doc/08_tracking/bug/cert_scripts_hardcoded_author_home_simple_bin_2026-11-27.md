# cert scripts defaulted SIMPLE_BIN to one author's home directory (2026-11-27)

`scripts/check/cert/{fuzz-diff,soundness-diff,stress-suite,run-tool-qual-corpus,freeze-tool-qual-golden}.shs`
defaulted `SIMPLE_BIN` to `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`, and
`tool-qual-meta.shs` to `$REPO_ROOT/bin/simple`. On any other host or checkout the default binary does not
exist. Found by the six `*_default_path_contract_test.shs` tests (unwired census).

Fix: all six default to `$REPO_ROOT/bin/release/x86_64-unknown-linux-gnu/simple`;
`freeze-tool-qual-golden.shs` gained the `SCRIPT_DIR`/`REPO_ROOT` it lacked. Two of the tests
(freeze, meta) also had a legacy-mutant step that referenced an unset `$repo` under `set -u`; they now
pass `repo='$repo'` to the mutant, and the meta test tolerates the mutant's own non-zero exit.

Status: fixed, verification-pending (tests green on Linux; the scripts were not run against a real
deployed binary). Prevention: the six tests pin the default path.
