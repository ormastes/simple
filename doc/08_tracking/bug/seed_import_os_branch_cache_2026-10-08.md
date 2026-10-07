# Seed imports bypass OS-branch preprocessing

The fresh bootstrap-only seed `ce6b74e018d71dd629b9218035f09a964eb07182aad33d438f14f16d6e32ffa0`
reported read/parse warnings for existing release sources during the
`051ee9d9780` Phase2 build: `app.cli.shard_mem_clamp`,
`std.nogc_sync_mut.io.windows_image_owner`, `path_identity`,
`path_identity_abi`, and `_PathIdentityPosix.errno_abi`.
These files contain valid `@when(os=...)` blocks. The Phase2 build subsequently
compiled 1209 modules with zero failures; these warnings are not evidence that
this defect caused the separate earlier compiler memory failure.

Native discovery already selects OS branches, but HIR's
`parsed_imported_module` and package-sibling loader used the shared source
cache, which passed original text directly to the parser. The generic warning
hid the cached parse error. A real Rust integration test against unchanged
production code reproduced rejection of a valid conditional import.

## Repair

Reuse `strip_os_when_blocks` before shared parsing, preserving original text
and line positions. Extend the existing bounded parsed and released-text cache
keys from physical path to `(physical path, target OS)`. HIR import paths pass
`native_project::effective_target().os`, the native compilation target owner;
they do not guess the host OS. Existing interpreter APIs retain host defaults.
AST borrowing, bounded retention and host ownership transfer remain in place.
Malformed directives remain errors, including in inactive branches.

The focused integration test checks valid host import parsing, Linux/Windows
same-path branch separation and repeated same-target cache identity, malformed
directives for both targets, and the five actual release owners under Linux,
Windows, FreeBSD and macOS. This is parser/cache evidence, not execution of
Windows or other target binaries.

## Retained qualification

Test base: `bb89cdd4f59ef0846e437849d71558411c4e59f5`.
Landing base: `4cf7793a7613d61fcc3483784c00e2752055aa47`; conflict-free
rebase preserved all three production-file and test-source SHA256 identities.
The green regression was not repeated after this unchanged-source rebase.
Isolated source:
`/var/tmp/simple-cfg-import-target-cache-20261007`. Evidence:
`/var/tmp/cfg-import-target-cache-20261007`.

- Baseline: actual focused test **0 passed, 1 failed**, rejecting the valid
  OS-conditional import; `baseline.log`, receipt and input hashes retained.
- Candidate cycle2: compilation failed because the interpreter facade's
  explicit re-export list omitted the new target APIs. No tests executed.
  A private ownership helper was also removed from the external test rather
  than changing its visibility. `candidate.log` retains the failure.
- Final cycle3: **4 passed, 0 failed, 0 ignored, 0 filtered**, actual native
  Rust integration executable, 0.02 seconds after 5m31 compilation.
  `candidate-cycle3.log` and receipt record exit0 and peak2940880 KiB.
  Exact source hashes and patch are retained in `candidate-cycle3-inputs.sha256`
  and `candidate-cycle3.patch`. Test ELF SHA256:
  `09f58e9741e4654c3f0d0164fbf1268d3de2ac589c9f9279f0d5a36481da4ed2`.
  No further regression run was performed.

Builds use a private copy of the completed runtime/seed Cargo cache, offline
locked dependencies, test profile, one job, an enforced 5859375 KiB process-tree
cap and 1800-second timeout. Live Phase2 source and caches are not modified.
Two preliminary direct-rlib link attempts failed on Cargo's split-metadata
layout before test execution; they are not regression verdicts.

## Separate remaining limitation

`interpreter_module/module_loader.rs` around lines1008–1036 reparses original
source after architecture filtering when that filtering changes the source.
That fallback can still reject a module mixing OS branches and inactive
architecture globals because it bypasses OS selection. This preexisting
interpreter route is outside this native-import repair. A focused combined
OS/architecture interpreter regression and repair remain necessary; no claim
is made that this change fixes every interpreter conditional-source route.
