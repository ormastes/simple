# Stage 2 candidate sanity SIGILLs: `env_get` recurses into itself via duplicate co-compiled definitions

- **Filed:** 2026-09-26
- **Status:** OPEN — blocks Stage 2 admission, therefore Stage 3/Stage 4, the
  self-hosted CLI, and the native MCP/LSP server artifacts
- **Area:** cross-module symbol resolution / co-compiled duplicate dispatch
  (interpreter + JIT), `std.env`
- **Host:** yoon-note, x86_64-unknown-linux-gnu
- **Tree:** clean `origin/main` @ `c7e695bcff0` (NOT a stale-tree artifact — see below)

## Symptom

`sh scripts/bootstrap/run-phase1-local.shs --jobs=4` builds the Rust seed, clears
preflight, compiles Stage 2, then aborts at Stage 2 admission:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

`rc=132` is SIGILL. Reproduced directly against the stage-2 lane's own binary:

```
C=.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple
SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 \
  "./$C" native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o /tmp/cand.bin
# -> Illegal instruction, rc=132
```

## Root cause: `env_get` calls itself

The run prints its own cause before dying:

```
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'env_get'
```

and, in the same log, the dispatch warning that explains why:

```
public function `env_get` has 4 co-compiled definitions with 2 differing signatures
  ((text)->Optional(text) vs (text)->text)
public function `env_get` has 6 co-compiled definitions with 2 differing signatures
  ((text)->Optional(text) vs (text)->text)
```

The warning text states the failure mode explicitly: *"JIT call sites resolve by
exact arg-type match (mangled `$dupN` variants), falling back to the last
definition when types are ambiguous — a fallback hit may still dispatch to the
wrong one."* Here the wrong one is **itself**: the `(text) -> text` wrapper's
internal call to the `(text) -> Optional(text)` overload resolves back to the
wrapper, so `env_get` recurses until the 1000-frame limit and the process traps.

The same log carries **72** distinct `co-compiled definitions with N differing
signatures` warnings (`_sha256_k`, `dir_create`, `file_read_text`, `join`,
`spawn`, `shell`, `process_wait`, …), so `env_get` is the first one to be hit on
this path, not the only latent instance. Anything that resolves by
"last definition wins" is a live mis-dispatch risk.

## Why two distinct definitions of `env_get` are co-compiled at all

The two signatures are the typed `Optional`-returning accessor and a
`text`-returning convenience wrapper. They become *co-compiled duplicates* — not
one module importing the other — when the compile closure pulls in more than one
copy of the same logical module. The stage-2 lane compiles under a sandboxed
`HOME`/`SIMPLE_LIB` with an SCV snapshot root
(`build/scv_snapshots/scv_revision_v1_<sha>/…`, cf.
`doc/08_tracking/bug/simpleos_cm33_policy_symbols_mangled_2026-09-26.md` where the
same snapshot root leaked into mangled symbol names), which is the obvious
candidate for how one logical module reaches the closure twice. **This part is a
hypothesis, not established** — the duplicate *count* rising 4 -> 6 within a single
run is consistent with it but does not prove it.

## It is NOT tree staleness, and NOT the seed's own native-build defect

Two confounds were ruled out explicitly:

- **Stale tree:** first observed on a working copy 1770 commits behind. Re-run on
  a clean `git checkout --force origin/main` (`c7e695bcff0`) with all current
  fixes present: identical failure. So it reproduces on mainline.
- **The separate seed-side `native-build` SIGILL**
  (`doc/08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`,
  fixed) is a *different* defect with a different mechanism (`ud2` at codegen
  entry from an empty backend table). Proof they are distinct: with that fix in
  place the **seed** builds the very same fixture successfully, both positionally
  and with `--source/--entry`:
  ```
  seed native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o out   -> rc=0
  seed native-build --source <dir> --entry hw.spl -o out                               -> rc=0 (cranelift and llvm)
  ```
  Only the stage-2 lane's binary traps, and it traps with a stack overflow in
  `env_get`, never with `ud2`.

## Unblock condition

`"./$C" native-build scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o /tmp/x`
exits 0 for the stage-2 candidate, and `run-phase1-local.shs --stop-after-stage2`
reaches an admitted Stage 2.

Suggested order of attack:

1. Establish *why* `std.env` is co-compiled twice on this path — dump the compile
   closure for the stage-2 invocation and look for one logical module present
   under two paths (repo path vs SCV snapshot path is the prime suspect). Fixing
   the duplication removes the ambiguity at its source and would clear many of
   the other 71 warnings too.
2. Independently, make ambiguous duplicate dispatch **fail closed** instead of
   "falling back to the last definition". A self-recursive resolution is never
   correct, and today it is reported only as a warning; a hard error at resolution
   time would have named this in one line instead of a SIGILL 1000 frames later.
3. Do **not** paper over it by raising the 1000-frame recursion limit — the
   recursion is unbounded, so a larger limit only delays the trap.

## Related

- `doc/08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`
  — the seed-side native-build SIGILL (fixed); its still-open follow-up is that the
  parent's failure relay can itself report SIGILL instead of the worker's message,
  which is worth keeping in mind when reading `rc=132` from any bootstrap lane.
- `doc/08_tracking/bug/simpleos_cm33_policy_symbols_mangled_2026-09-26.md` — same
  SCV snapshot root leaking into symbol identity, fixed there for
  `__module_init_*`.
- Stage 2 is under active repair (60 stage2-related commits on `main` in the three
  days before this record); re-check against a newer `main` before investing.
