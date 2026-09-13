# Stage 3 comparator binding fails on any macOS host whose `cmp` is a Homebrew symlink (2026-09-13)

Status: **OPEN — blocks every macOS bootstrap lane at the pipeline entry, after the
Rust seed builds.** Landed `863438ffac8` (Sat Sep 12 10:49 +0900, "feat(bootstrap):
Windows full bootstrap toolchain suite"), i.e. a fresh regression.

## Verdicts, verbatim

Default environment (Homebrew `diffutils` on PATH ahead of `/usr/bin`):

```
error: could not bind canonical Stage 3 comparator
```

With the documented override `BOOTSTRAP_STAGE3_COMPARE_TOOL` pointed at either
`/usr/bin/cmp` or the Cellar canonical path (with and without
`BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256`), it gets one step further and then dies:

```
error: Rust runtime authority private-admission origin comparator unavailable or I/O
failed: .../stage3/aarch64-apple-darwin/runtime-origin-before.txt
        .../stage3/aarch64-apple-darwin/runtime-origin-after.txt status=2
error: Rust runtime authority changed during private admission
```

The second message is misleading: `diff` of those two files is EMPTY. Nothing changed;
the comparator itself returned 2.

## Mechanism

`scripts/check/lib/bootstrap-stage3/authority.shs`:

- `bootstrap_stage3_canonical_path` (:486) rejects its input outright when the path AS
  GIVEN is a symlink (`[ ! -L "$input" ] || return 1`) — it does not resolve it.
- `bootstrap_stage3_compare_bind` (:26) canonicalises `command -v cmp`; on a Homebrew
  host that is `/opt/homebrew/bin/cmp -> ../Cellar/diffutils/3.12/bin/cmp`, a symlink,
  so the bind returns 2. That is the first verdict.
- `bootstrap_stage3_compare_files` (:51-56) independently RE-RESOLVES the ambient `cmp`
  on every comparison and requires `canonical_file(ambient) == BOOTSTRAP_STAGE3_COMPARE_TOOL`.
  So pinning the override cannot help while the ambient `cmp` is still the symlink —
  which is why runs with the override also fail, at status 2. That is the second verdict.
- The override additionally requires `BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256` to be set in
  the same environment (:60-62); setting the tool alone is silently insufficient.

## Workaround (used to get past it)

Put a NON-SYMLINKED `cmp` first on PATH and pin the tool to the same path:

```
env PATH=/usr/bin:$PATH BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp \
  sh scripts/bootstrap/bootstrap-from-scratch.sh ...
```

Do not truncate PATH to just `/usr/bin:/bin` — that loses the toolchain and the run dies
earlier with `error: failed to fingerprint Rust seed inputs`.

## Suggested fix (not applied here — this is a peer's anti-alias hardening design)

Resolve symlinks and compare the RESOLVED target, instead of rejecting any path that is
itself a symlink: the anti-alias property that is actually wanted is "ambient and pinned
comparator are the same inode/content", and a Homebrew symlink satisfies that. If the
strict form is deliberate, the override must be made sufficient on its own (bind should
accept an explicitly pinned tool without also demanding a matching non-symlinked ambient
`cmp`), and the requirement to set the `_SHA256` companion must be documented.

Found while verifying
`doc/08_tracking/bug/macos_seed_build_duplicate_rt_process_twin_symbols_2026-09-13.md`
(fixed by PR #718); this is the NEXT blocker on the same lane.

## RESOLVED 2026-09-13 — it was a STALE-SNAPSHOT CLOBBER, not an unfixed defect

PR #670 (`418399c2d84`, "fix(bootstrap): accept a symlinked cmp ...") DID land the
fix: a portable `bootstrap_stage3_resolve_symlinks` (walks the chain, resolves a
RELATIVE target against the LINK's directory, caps at 32 hops), a
`compare_bind` that binds the RESOLVED physical target, and a `compare_files`
that uses the BOUND path instead of re-resolving the ambient `cmp` on every
comparison. Four fixtures went into `self-test.shs`, including the symlinked-cmp
regression.

One of the four later commits that touched
`scripts/check/lib/bootstrap-stage3/authority.shs`
(`3f005ff07a2`, `c4d3c9e738f`, `621a4d6b2ab`, `80c1099f466`) re-snapshotted a
STALE copy of that file and reverted the comparator half wholesale, while the
self-test half survived in its own file. The tree therefore carried a selftest
calling `bootstrap_stage3_resolve_symlinks` against an `authority.shs` that no
longer defined it — fixture 1/4 died at `command not found` and the bind was back
to `[ "$candidate" = "$canonical" ] || return 2`. That is why the bug "reappeared"
after #670. `git diff 418399c2d84 HEAD -- .../authority.shs` shows the revert as
two hunks of pure deletion, alongside one genuine forward delta (the
`SIMPLE_LLVM_BIN LLVM_SYS_180_PREFIX PATH` addition to
`bootstrap_stage3_stage2_canonical_env_names`).

Fix applied here: re-apply exactly the two comparator hunks, KEEPING the env
allowlist forward delta. No new design; #670's design was already right.

Verified on this host with the stock Homebrew-first PATH and **no** `/usr/bin`
workaround (`command -v cmp` = `/opt/homebrew/bin/cmp` ->
`/opt/homebrew/Cellar/diffutils/3.12/bin/cmp`):

```
which cmp: /opt/homebrew/bin/cmp
resolved:  /opt/homebrew/Cellar/diffutils/3.12/bin/cmp
bind of a symlinked fixture cmp -> binds the PHYSICAL target, not the link
```

`bootstrap_stage3_provenance_self_test` now runs all four comparator fixtures and
proceeds past them (1/4 symlinked bind, 2/4 no-cmp = ERROR 2, 3/4 `#!` wrapper
refused, 4/4 shadowed pin refused). The suite still returns 1 further downstream,
in `bootstrap_stage3_seed_inputs_fingerprint`, which refuses an empty
`abi_policy` argument — a **separate, pre-existing** red with no relation to the
comparator, not introduced or repaired here.

Status: **CLOSED** (comparator). The lesson is the clobber, and it is the third
instance of the class `.claude/rules/vcs.md` § "Sync must never clobber"
describes: a whole-file snapshot taken before a fetch silently rewinds another
session's landed fix while the commit that carries it looks like forward
progress.
