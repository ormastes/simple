<!-- codex-research -->
# Next Beta, Full Bootstrap, and SimpleOS Multiarch — Domain Research

Date: 2026-07-30

## Release identity

GitHub releases are tied to tags, and GitHub CLI supports an explicit
`--prerelease` flag. A second beta therefore needs a new immutable tag and a
matching canonical version; moving the existing `v1.0.0-beta` tag is not a safe
release mechanism.

Sources:

- GitHub, “Managing releases in a repository”:
  https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository
- GitHub CLI, `gh release create`:
  https://cli.github.com/manual/gh_release_create

## Multi-platform workflow shape

GitHub Actions matrices are the native mechanism for required per-platform and
per-architecture jobs. Workflow artifacts are the native handoff between build,
verification, and release jobs. Release creation should consume verified
artifacts rather than rebuild or weaken evidence.

Sources:

- GitHub, “Running variations of jobs in a workflow”:
  https://docs.github.com/en/actions/how-tos/write-workflows/choose-what-workflows-do/run-job-variations
- GitHub, “Workflow artifacts”:
  https://docs.github.com/en/actions/concepts/workflows-and-actions/workflow-artifacts

## Target confidence

Target availability is not the same as native-host proof. Rust's platform
support documentation distinguishes targets with host tools and automated
testing from build-only targets. The release must make the same distinction:
cross-compiling an object or packaging source is not a full bootstrap pass.

Source:

- Rust compiler platform support:
  https://doc.rust-lang.org/rustc/platform-support.html

## Applied conclusions

- Use a new beta tag/version and publish it as a prerelease.
- Use required matrices and verified artifact handoff.
- Label cross-compile-only evidence honestly; it cannot satisfy a requested
  full-bootstrap target.
- Keep macOS proof in native GitHub runners.
- Require real SimpleOS boot/runtime and compiler-in-filesystem evidence for
  each released architecture, not merely a nonempty kernel file.
