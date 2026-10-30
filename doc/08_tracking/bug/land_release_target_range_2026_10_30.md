# Landing local gates used the main range for release branches

`LAND_TARGET_REF=release/1.0.0 sh scripts/check/land.shs --dry-run` resolved
the correct release base for the integrity gate, but passed only `--rev` to
`run-gate-tier.shs`. The runner then derived `origin/main..TIP`. A one-commit
provider backport consequently selected 3,221 commits in the local tier and
remained active after 15 minutes. The observed provider head was `73f45e0c`
with parent `70cd249`; quick rules and integrity had already passed.

The wrapper now passes both its pinned `--base` and `--range BASE..TIP` to
the runner, keeping `{base}`, `{range}`, and `{rev}` bound to the same
protected-target snapshot. The standalone runner's default stays unchanged.

Regression: `sh scripts/check/check-land-target-range.shs` executes the actual
landing wrapper and tier runner with a single real range-checking manifest
row in a temporary Git repository. Rules and signing are boundary doubles;
this test does not qualify the production gate suite or cryptographic signing.
It checks release history differing from main, release without main, default
main, rejection of a failing local row before signing, and a missing target
ref failing before dispatch. All five cases passed on Windows Git Bash. A
negative control using the original wrapper failed the first release case.
The required-gates workflow runs this regression as an explicit step.
