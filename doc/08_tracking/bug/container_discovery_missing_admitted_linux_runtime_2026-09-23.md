# Container discovery has no admitted Linux runtime on a clean checkout

Status: OPEN — separate from the Bash invocation fix.

The container discovery jobs in `.github/workflows/containerized-tests.yml`
mount the checkout at `/workspace`. `tools/docker/Dockerfile.test-isolation`
contains dependencies and a Bash entrypoint; it does not bundle Simple.
The required `bin/release/x86_64-unknown-linux-gnu/simple` is an untracked build
artifact. The build-container job publishes only the dependency image, and
the discovery jobs neither build nor download an admitted runtime.

At PR #1328 head `86a04e16b36a50f5898c139172e0387e0141bb7a`, the
[Docker unit discovery job](https://github.com/ormastes/simple/actions/runs/35720609061/job/106993446105)
failed earlier with `test: test: Is a directory`, exit 126: Bash was passed
`test` as its script path. Explicit `bash -c 'exec ... "$@"' -- test ...`
fixes that command dispatch, but clean checkout discovery remains blocked
because the intended executable is absent. The old image `--version` check
only printed Bash's version and did not establish Simple availability.

Resolution requires provisioning a verified self-hosted Linux runtime to each
consumer job, with artifact identity and admission evidence. A Rust seed must
not be copied into the production runtime path to make discovery green.
This is a separate artifact-provisioning change; no compiler build or runtime
substitution is included in the invocation fix.

Focused verification: `node scripts/check/check-container-discovery-invocation.cjs`
reproduces exit 126 with a `test/` directory and exercises all eight actual
workflow discovery/resource commands against a fake runtime, checking exact
arguments and nonzero exit propagation. This proves dispatch only, not
compiler behavior, test discovery, container limits, or production admission.
