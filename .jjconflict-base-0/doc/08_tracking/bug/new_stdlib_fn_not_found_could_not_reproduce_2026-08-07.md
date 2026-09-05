# "new function not found" after adding fn to existing stdlib .spl — could NOT reproduce

Date: 2026-08-07
Status: unable to reproduce; treating as false alarm pending further evidence

## Reported finding (sibling investigation, this session)

Adding a brand-new top-level `fn zzz_probe_fn(x: i64) -> i64: x + 1` to an
existing, previously-working stdlib file and calling it from a spec was
reported to fail with `semantic: function `zzz_probe_fn` not found`, allegedly
reproduced in TWO files — `src/lib/common/crypto/aes_gcm.spl` and
`src/lib/common/hash/djb2.spl` — under THREE engines (`bin/simple run` JIT
w/ interpreter fallback, `SIMPLE_EXECUTION_MODE=interpreter`, and
`bin/simple test`). Pre-existing functions in the same files were said to
resolve/execute correctly.

## What I did

Reproduced against the exact two named files plus a third
(`src/lib/common/hash/adler32.spl`), varying every dimension the report
mentioned:

1. `adler32.spl` — appended `fn zzz_probe_fn(x: i64) -> i64: x + 1` (no
   explicit `export` line; file has no export list, so top-level `fn` is
   auto-exported). New throwaway spec `use std.hash.adler32.{adler32,
   zzz_probe_fn}` + `it` block calling it via `bin/simple test`. **PASSED**
   (2 examples, 0 failures).
2. `djb2.spl` — appended `fn zzz_probe_fn2` **without** adding it to the
   file's existing explicit `export djb2_hash_text` list (to test an
   export-list-staleness hypothesis). New throwaway spec via `bin/simple
   test`. **PASSED** — resolved even though never added to the export list,
   ruling out an export-index-cache hypothesis.
3. Same `djb2.spl` addition, called instead from the pre-existing, already
   test-manifest-registered `test/01_unit/lib/common/hash/djb2_spec.spl`
   (added an `it` block importing `zzz_probe_fn2` alongside the file's other
   4 passing examples) via `bin/simple test`. **PASSED** (5 examples, 0
   failures) — rules out "only reproduces on a brand-new, never-indexed spec
   file."
4. `aes_gcm.spl` (the second file named in the report) — appended
   `fn zzz_probe_fn3`, new throwaway spec `use std.crypto.aes_gcm.{
   zzz_probe_fn3}` via `bin/simple test`. **PASSED** (1 example, 0 failures).
5. Separately, a scratch `.spl` script importing `djb2.zzz_probe_fn2` was run
   via both `bin/simple run` (default JIT) and `SIMPLE_EXECUTION_MODE=
   interpreter bin/simple run` — **both printed `42` correctly**, no "not
   found" error, no fallback-triggered failure.

All edits were reverted immediately after each probe (content diffed byte-
for-byte against a `/tmp` backup taken before editing; `grep -l zzz_probe`
across all touched files returns empty post-cleanup). No cache directory
(`.simple/`, `build/*cache*`) was manually cleared at any point during these
probes — none was needed.

## Environment note (unrelated tangent, recorded for completeness)

`bin/simple` in this WC resolves to `bin/release/x86_64-unknown-linux-gnu/
simple`, which prints `WARNING: this Rust-built Simple binary is a bootstrap
seed only` on every invocation — i.e. the currently-deployed `bin/simple` is
the Rust seed, not the self-hosted pure-Simple binary the project's own rule
(`Default tooling = pure-Simple self-hosted binary`) calls for. `bin/simple
test` additionally spawns a `child binary: .../release/x86_64-unknown-linux-
gnu/simple` subprocess (same seed). This is consistent with the existing
memory note that `simple test` delegates to the Rust seed. If the sibling
investigation's binary was in a different state (e.g. mid-redeploy, briefly
pointing at a stale self-hosted build), that could in principle explain a
transient divergence, but I could not find any evidence of that — the seed
was the only binary present at both investigation times as far as I could
tell.

Separately (not connected to the finding above, but discovered while
picking probe files): `git ls-tree -r --name-only HEAD -- src/lib/common`
returns **zero** entries even though `git log -- src/lib/common/<file>`
shows real history and 815 files exist on disk under that directory —
i.e. the entire `src/lib/common` subtree is currently absent from HEAD's
committed tree (matches the "exists on disk, but not in HEAD" symptom
documented in prior session memory about tree wipes). This is a VCS/index
state issue, not a compiler runtime issue — the interpreter/JIT resolve
modules from the filesystem, not from git — and does not explain the
reported "function not found" (the pre-existing functions in the same
files resolve fine, on disk, regardless of git tree state). Flagging it
here only because it's alarming and adjacent; it deserves its own look
using the existing tree-size-guard tooling, separately from this
investigation.

## Conclusion

Could not reproduce the "new function not found" behavior under any
combination tried (2 of the reporter's exact files, 3 engines, both
new-spec and existing-registered-spec call sites, with and without adding
the new symbol to an explicit export list). No stale-cache directory was
found or needed to be cleared. No fix was made because there is nothing
here to fix — the mechanism as reported does not reproduce.

Recommend the original finding be re-verified with exact transcripts
(command, file paths, timestamps, `bin/simple --version` / `readlink -f
bin/simple` output at the time) before treating
`reference_compiler_spl_edits_are_live_under_bin_simple_test.md` as
contradicted or too broad — nothing found here narrows its scope. This is
not connected to the incremental-cache fix landed at `5b569e96986d` in
this session as far as I could determine; I found no cache path that
`bin/simple test`/`run` module resolution reads which that commit touches
or which needed invalidating.

---

# RESOLVED — 2026-08-08 (third-party claim audit)

**Both agents were reporting real observations. The reproducer is the location
of the ENTRY FILE, not the stdlib file, and neither investigation varied it.**

Status: **RESOLVED — not a compiler defect.** The "could not reproduce" verdict
above is correct for the case it tested (entry file inside the repo). The
original report is also a real, reproducible behaviour — under a condition
neither investigation controlled for.

## Probe

Positive-control design: one PRE-EXISTING stdlib fn and one NEWLY-ADDED
unexported fn, imported from the same `use` line of the same file, so a module
that fails to load at all cannot masquerade as "the new symbol is missing".

Appended to a clean `src/lib/common/convert.spl` (a file with **no** export
list, byte-identical to its `origin/main` blob beforehand):

```
fn audit_probe_new_stdlib_fn(n: i64) -> i64:
    n * 7 + 3
```

Caller: `use std.common.convert.{i64_to_text, audit_probe_new_stdlib_fn}`.

| entry file location | engine | control (`i64_to_text`) | subject (new fn) |
|---|---|---|---|
| `test/01_unit/lib/common/zz_audit_probe_spec.spl` (in repo) | `bin/simple test` | PASS | **PASS** |
| `./zz_audit_probe_run.spl` (in repo root) | `bin/simple run` (JIT) | `control=41` | **`subject=45`** |
| `<scratchpad>/probe_run.spl` (outside repo) | `bin/simple run` (JIT) | `control=41` | **`error[E1002]: function ... not found`** |
| `<scratchpad>/probe_run.spl` (outside repo) | `SIMPLE_EXECUTION_MODE=interpreter` | `control=41` | **`error[E1002]: function ... not found`** |

In-repo spec verdict line, verified with `/usr/bin/grep -a`:

```
SPEC FILE VERDICT: test/01_unit/lib/common/zz_audit_probe_spec.spl declared>=2 executed=2 passed=2 failed=0 dropped=0
```

## Mechanism

When the entry `.spl` lives outside the repo, the compiler infers an **implicit
source root from the entry file's own directory** and resolves `std.*` against
it. The diagnostic names the bogus path outright:

```
[use-warning] 'audit_probe_new_stdlib_fn' is named in `use std.common.convert.{...}`
  but module '<scratchpad>/src/lib/common/convert.spl' does not provide it
```

`<scratchpad>/src/lib/common/convert.spl` does not exist. Pre-existing stdlib
symbols still resolve through a separate builtin/registry path, so the control
passes — which is exactly why this presents as "**only** the new function is
invisible, old ones work fine, under **every** engine." The engine-independence
that made it look like a deep compiler defect is just the tell that it happens
during module resolution, upstream of engine selection.

## Why each investigation got the answer it got

- Report #1 almost certainly ran its probe script from a scratch/`/tmp` path
  (the natural habit for a throwaway probe) and hit the implicit-source-root
  resolution. Real observation, wrong diagnosis.
- Report #2 used `bin/simple test` on repo-relative spec paths throughout — all
  five probes stayed inside the source root, so the condition never arose. Real
  non-reproduction, correct conclusion, incomplete explanation.

Neither is "wrong". The missing variable was the entry file's path.

## The corrupted-HEAD-tree confound: ruled out

This WC's local HEAD commit has a truncated git tree (`git ls-tree -r HEAD --
src/lib/common` returns 0 entries while the files exist on disk). It is **not**
the explanation: the in-repo probes above passed under exactly that corrupted
HEAD. Module resolution reads the filesystem, not git. Ruled out empirically,
not by assumption.

## Consequence for other docs

`doc/08_tracking/bug/credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`
cited this "blocker" as the reason a real AES-CBC fix could not be verified or
landed. **That blocker is void** — a new stdlib function is verifiable today by
any in-repo spec. See the claim-audit section of that doc.

## Memory/rule narrowing

The standing note that ".spl edits are LIVE on the interpreter path (no
bootstrap rebuild needed)" is **confirmed** — but needs one qualifier:

> …live **provided the entry file resolves against the repo source root**. An
> entry script outside the repo silently re-roots `std.*` at its own directory,
> where pre-existing stdlib symbols still resolve via the builtin registry
> while newly-added ones raise `E1002 function not found` under every engine.
> Keep probe scripts inside the repo, and read the `[use-warning]` line — it
> prints the resolved module path and gives the mechanism away immediately.

## Cleanup

All probe artifacts reverted: `src/lib/common/convert.spl` md5 restored to its
`origin/main` blob, `zz_audit_probe_spec.spl` and `zz_audit_probe_run.spl`
deleted, `grep -c audit_probe` over `src/`+`test/` returns 0.
