# BuildRunner native publication drops executable permissions

Status: fixed in source; deployed compiler/runtime artifacts are not rebuilt.

## Reproduction and impact

`builder_cli_publish_one_v1` in `src/app/buildrunner/cli_files_v1.spl` copies
the admitted artifact to a private staging file using `file_copy`, then
publishes it with `file_publish_noreplace`. Both C providers of `rt_file_copy`
created that copy with `fopen(..., "wb")` and never restored source permissions.
A compiler-produced executable could therefore pass output digest validation
and publication while its published copy could not be executed. Content hashes
do not detect the missing execute permission.

The Rust runtime delegates to `std::fs::copy`, so interpreter-only coverage
does not reproduce the C runtime defect. The native selfcheck exercises the
real functions in `runtime.c` and `runtime_native.c` independently.

## Fix

Both C implementations read the opened source's mode with `fstat`, flush the
copied bytes, and apply its ordinary POSIX permission bits through `fchmod`
on the open destination. This preserves executable/data distinctions despite
the manager's umask or a pre-existing destination's permissions. Privilege and
special mode bits are not propagated. Windows retains its existing permission
behavior. Source read, flush, permission, and close failures return failure.

The process ownership V4 guard, compiler execution, and BuildRunner receipt
contracts are unchanged.

## Evidence

Command: `sh scripts/check/check-runtime-file-copy-mode.shs`

- Red on the parent revision: both providers report `copied mode 600, expected
  751` and the check exits 1.
- Green after the fix: both providers pass copy, no-replace publication, actual
  execution with expected exit 37, ordinary data-file mode replacement, and
  missing source/destination-parent failures.
- The check compiles only the two C runtime providers and the small selfcheck;
  no compiler/P2 rebuild is performed. Temporary artifacts are removed.

This proves publication preserves an executable artifact on macOS. It does
not claim that the complete Hello native compiler/BuildRunner path has run.

## Required Gates wiring correction

PR #5214's Required Gates run 40784628246 failed
`local-range-shs-hygiene`: the new native selfcheck wrapper had no enforcement
root. The C regression itself was passing, but a manual invocation did not
make it part of the automated suite.

The dedicated `runtime-file-copy-mode.yml` workflow now invokes the real
wrapper on Ubuntu for pull requests and pushes to main and release branches
that change the C runtime, wrapper, or workflow. Its sparse checkout includes
both providers and their headers plus the test fixture. A failed copy,
publication, execution, or mode assertion fails the job. No opt-out, baseline
exemption, or weakened hygiene check is used. The POSIX fixture is not added
to the cross-platform bootstrap registry: Windows does not implement POSIX
execute permissions, and its explicit SKIP must not become a bootstrap FAIL
or a fabricated PASS.

## Remaining recovery gap

Previously published files are not repaired by this change. BuildRunner's
existing-destination and cached-output admission paths compare regular-file
status and content hashes only. An output already published without execute
permission can therefore remain a verified cache hit after this runtime fix.
Use a fresh private output/state directory when validating the fixed runtime.

A separate BuildRunner change must define and validate executable-mode
evidence (or an explicitly declared executable-output contract) before it can
repair or reject such cached artifacts. The current receipt schema records
paths and digests, so blindly chmodding every output would wrongly mark object
and data files executable. This recovery work remains open; the current fix
prevents loss of mode on new C-runtime copies only.
