# Cache writer live GitHub Actions verification

- **Filed:** 2026-09-23
- **Status:** deferred until the workflow change is present on the remote branch
- **Component:** `.github/workflows/cache-main-writer.yml`, `.github/workflows/cache-branch-ci.yml`

## Deferred live evidence

Static regression coverage proves that clean-checkout cache writers provision
`bin/simple`, disabled branch-cache runs skip compiler setup and build work, and
cache promotion remains free of compiler provisioning. Local execution cannot
prove hosted-runner behavior or secret-backed writer admission.

After this change reaches GitHub, dispatch or observe:

1. `cache-main-writer` on `main`: require the runtime provisioning step and
   **Build the exact main commit** to pass from a clean hosted checkout. Record
   Stage 2/Stage 4 admission and peak RSS from the bounded two-job bootstrap.
2. `cache-branch-ci` with the namespace disabled: require the Cargo cache,
   runtime provisioning, build, and publish steps all to be skipped.
3. `cache-branch-ci` with the namespace enabled on an authorized branch:
   require provisioning and build to pass before best-effort publication.
4. `cache-promotion`: require validation to run without Rust/Cargo/compiler
   setup steps.

Record run URLs and conclusions here, then mark this TODO resolved. Do not
substitute an obsolete net-zero revert branch for these live runs.

The current source tree does not contain a `SIMPLE_CACHE_MAPPINGS_OUT`
producer. Publication already treats an absent mappings file as best-effort;
live verification must report that absence honestly rather than adding a
static nonempty-file assertion that would make every clean build fail.
