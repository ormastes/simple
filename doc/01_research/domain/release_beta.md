# Release Beta Domain Research

GitHub Actions artifacts are the supported mechanism for passing produced binaries and logs between jobs; dependent consumers should use `needs` and download the named artifact only after the producer succeeds. Artifact upload supports `if-no-files-found`; release-producing paths should select `error`, not the default warning, for required payloads.

The workflow-provided `GITHUB_TOKEN` is a repository-scoped installation token and can authenticate `gh release create` when the job has explicit `contents: write`. A release job must still fail before creation when its required artifact set is empty or incomplete.

Artifact metadata includes a SHA-256 digest, and release packages should additionally retain their project checksum files and validate the unpacked payload contract before upload. Build cache is not artifact evidence and cannot replace produced release binaries.

Primary references:

- GitHub Docs, “Workflow artifacts”: https://docs.github.com/en/actions/concepts/workflows-and-actions/workflow-artifacts
- GitHub Docs, “Store and share data with workflow artifacts”: https://docs.github.com/en/actions/tutorials/store-and-share-data
- GitHub Docs, “GITHUB_TOKEN”: https://docs.github.com/en/actions/concepts/security/github_token
- Official `actions/upload-artifact` documentation: https://github.com/actions/upload-artifact
