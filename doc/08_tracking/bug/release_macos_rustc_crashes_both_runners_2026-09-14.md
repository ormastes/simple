# Release: `rustc` crashes on both macOS runners, blocking every release
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-14
**Impact:** `build-bootstrap` can never be green, so `whole-tests` and
`create-release` are skipped and **no tag can publish assets**. This is live on
`main`, not only on the `v1.0.1-beta.1` tag.
**Status:** root cause localised to the runner toolchain; fix not yet chosen.

## Symptom

Both macOS legs of the release matrix fail in `Build native macOS binary via
Rust bootstrap`, at the first `rustc` invocation — before any project code is
compiled:

| leg | runner | crash |
|---|---|---|
| darwin-x86_64 | `macos-15-intel` | `rustc` **SIGSEGV** ("failed to run `rustc` to learn about target-specific information") |
| darwin-arm64 | `macos-latest` | `rustc -vV` **SIGABRT** (signal 6) |

```
error: process didn't exit successfully:
  `/Users/runner/.rustup/toolchains/stable-aarch64-apple-darwin/bin/rustc -vV`
  (signal: 6, SIGABRT: process abort signal)
```

`rustc -vV` only prints a version string. A crash there means the installed
compiler cannot start at all, so nothing about this repo's source is implicated.

## Reproduced, not inferred

Measured on release run `34067963746` (tag `v1.0.1-beta.1`) by re-running the
failed jobs on 2026-09-14. Both macOS legs failed again, darwin-x86_64 in 3.5
minutes. Fresh job ids `103867701640` (intel) and `103867701531` (arm64) — new
attempts, not cached results. The same rerun turned six other legs green:
linux x86_64/aarch64/riscv64, windows x86_64/aarch64, freebsd-x86_64.

So the failure is deterministic and macOS-specific, on **both** architectures.

## Where it comes from

`.github/workflows/release.yml` installs the toolchain with:

```yaml
- name: Setup Rust toolchain (macOS/Windows)
  if: runner.os == 'macOS' || runner.os == 'Windows'
  uses: dtolnay/rust-toolchain@stable
```

`@stable` floats. The same unpinned action succeeds on `windows-latest`, so the
broken combination is specifically current-stable Rust against the current
macOS runner images. A pin to a known-good version is the obvious remedy, but
**which** version is known-good has NOT been established here — this host has no
macOS, so any pin is a guess until a CI run proves it. Do not land a pinned
version and claim it fixes this without a green macOS leg behind it.

## Why it blocks releases completely

`create-release` is gated on `whole-tests`, which is gated on `build-bootstrap`.
The matrix declares no `continue-on-error`, so either macOS leg failing takes
the whole job down and skips both downstream jobs. `create-release` never fails
— it never runs. That is why `v1.0.1-beta.1` has carried zero assets since
2026-09-06 while six platforms built fine.

`main`'s workflow is stricter still (it also requires `build-installers` and
`simpleos-build`), so re-cutting as `beta.2` does not avoid this.

## Options, none yet chosen

1. **Pin the toolchain** — smallest change, but needs a macOS CI run to verify.
2. **`continue-on-error: true` on the macOS legs** — unblocks releases
   immediately, at the cost of shipping without macOS assets and weakening the
   gate. Prefer only as a deliberate, recorded decision.
3. **Move macOS off `dtolnay/rust-toolchain@stable`** to an explicit rustup
   install with a chosen channel.

## Related

- `beta1_tag_cannot_bootstrap_on_windows_2026-09-14.md` — the Windows lane, and
  the gate analysis this record extends.

