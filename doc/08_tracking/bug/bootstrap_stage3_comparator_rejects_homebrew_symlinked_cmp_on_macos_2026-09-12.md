# Stage-3 comparator binding refuses a Homebrew-symlinked `cmp`, blocking every macOS bootstrap (2026-09-12)

Status: **FIXED 2026-09-12, PR #670.** Found while re-running lane 1 of
`doc/03_plan/infra/macos_open_bugs_fix_lanes_round2_2026-09-12.md`.

The suggested fix at the bottom of this record is what landed, plus the second
half the record correctly identified as necessary: `compare_files` no longer
re-resolves the ambient `cmp` at all, because shadowing is now decided ONCE at
bind time. `bootstrap_stage3_compare_bind` binds the PHYSICAL target, resolved
by a new portable `bootstrap_stage3_resolve_symlinks` (`readlink -f` is
GNU-only, so it walks the chain one link at a time, resolves a RELATIVE target
against the LINK's directory rather than the caller's cwd, caps at 32 hops, and
then uses the repo's existing `cd -P` canonicaliser). The anti-alias property is
carried by `BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256` exactly as this record
proposed: it pins the CONTENT, and an aliased name cannot change which bytes
run.

Every refusal path now prints a reason, so the misleading "Rust runtime
authority changed during private admission" no longer stands in for "the
comparator was refused". A `#!` script wrapper is REFUSED rather than receipted
-- the trust model is a byte-hash pin of the bound file, and a wrapper's own
bytes do not determine what actually runs, so hashing it would pin nothing.

The missing fixture this record called for is in place: four comparator cases in
`bootstrap_stage3_provenance_self_test` (symlinked `cmp` accepted and bound to
its physical target; no `cmp` on PATH -> 2; script wrapper -> 2; a pin shadowed
by a different ambient `cmp` -> 2). They are deliberately placed EARLY in that
function, because on macOS a later step (seed-stamp ABI policy) is
baseline-red and would otherwise stop the suite before they ran.

Verified on the real host with stock Homebrew-first PATH, NO `/usr/bin`
workaround and NO pin: binds `/opt/homebrew/Cellar/diffutils/3.12/bin/cmp`,
equal->0, differ->1. Two live `bootstrap-from-scratch.sh` runs in that
configuration cleared the bind, cleared Stage 1, and reached `Stage 2: admitted
parent`. The workaround below is no longer required.

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2
--full-bootstrap --mode=dynload` dies **before Stage 1** with:

```
error: could not bind canonical Stage 3 comparator
```

(`bootstrap-from-scratch.sh:2631`). This is upstream of Stage 2 entirely, so on
a stock macOS host the tracked Stage-2 `serialize_mir_function` SEGV is not even
reachable — which is a large part of why that bug has gone "not re-reproduced"
for two rounds.

## Root cause

`bootstrap_stage3_compare_bind` (`scripts/check/lib/bootstrap-stage3/authority.shs:26`)
takes `command -v cmp`, canonicalises it physically, and requires the two to be
**equal** — a deliberate anti-symlink-alias check:

```sh
bootstrap_stage3_compare_candidate=$(command -v cmp) || return 2
bootstrap_stage3_compare_canonical=$(bootstrap_stage3_canonical_file "$candidate") || return 2
[ "$candidate" = "$canonical" ] || return 2
```

On macOS with Homebrew `diffutils` installed — the common case, and present on
this host — `command -v cmp` resolves to `/opt/homebrew/bin/cmp`, which is
*always* a symlink:

```
lrwxr-xr-x /opt/homebrew/bin/cmp -> ../Cellar/diffutils/3.12/bin/cmp
-rwxr-xr-x /usr/bin/cmp
```

so `candidate != canonical` and the bind returns 2 unconditionally. The check is
correct in intent; it just has no way to accept a package-manager shim.

## Second gate behind the first

Setting the documented env knob `BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp` is
**not sufficient**. `bootstrap_stage3_compare_files` (`authority.shs:46-63`)
independently re-resolves the *ambient* `cmp` on every comparison and requires
it to equal the bound tool:

```
error: Rust runtime authority private-admission origin comparator unavailable
       or I/O failed: ... status=2
error: Rust runtime authority changed during private admission
```

— a misleading message: nothing changed, the comparator was simply refused. The
ambient `cmp` must itself be the canonical one.

## Proven workaround

Put `/usr/bin` ahead of Homebrew on PATH *and* pin the tool:

```sh
PATH="/usr/bin:$PATH" BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
     --full-bootstrap --mode=dynload --jobs=half
```

With this the lane clears the comparator, clears Stage 1, and reaches
`Stage 2: admitted parent -> bootstrap_main.spl`.

## Suggested fix (not applied here — it touches the provenance chain)

Accept a symlinked *candidate* as long as its canonical target is hashed and
pinned, which the code already does (`BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256`):
bind the CANONICAL path rather than requiring candidate == canonical, and have
`compare_files` compare the ambient tool's canonical form against the bound
canonical form. That keeps the anti-alias property — the bytes are still
hash-pinned — without making a package-manager shim fatal. A fixture must cover
a symlinked `cmp` on PATH explicitly; the current tests only ever see a direct
one, which is why this shipped.
