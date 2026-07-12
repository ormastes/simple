# native-build --entry-closure: "cannot convert array to int" parsing entry file (unreachable wall, newly exposed)

**Status:** OPEN — newly exposed, not yet root-caused.
**Severity:** Blocking for `native-build --entry-closure` end-to-end, but a
distinct wall from the compute-spin hang in
`native_build_entry_closure_quadratic_hang_2026-07-12.md`.
**Affected file:** unknown — surfaces inside interpreted
`parse_full_frontend` (compiler frontend) while parsing the entry file.
**Path:** `bug` track.

## Symptom

After fixing the O(n²) entry-closure hang (see the sibling bug doc), the same
repro command:

```bash
rm -rf build/bootstrap/native_cache
<seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 16 --cache-dir build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/main.spl \
  --runtime-path <repo>/src/compiler_rust/target/bootstrap -o <out>
```

now completes the entry-closure BFS and `phase1:load_sources` in 456ms, then
fails almost immediately in `phase2:parse`:

```
[BOOTSTRAP-PHASE] +456ms phase1:load_sources:done n_sources=493
[BOOTSTRAP-PHASE] +456ms phase2:parse:start
[BOOTSTRAP-PHASE] +457ms phase2:parse:file:start src/app/cli/main.spl chars=773
error: semantic: type mismatch: cannot convert array to int
```

`src/app/cli/main.spl` is a trivial 773-character file (three `export use`
lines + comments), so the failure is very unlikely to be about that file's
own content — more likely some shared/global interpreter state that this
specific pipeline configuration (`--backend cranelift --mode dynload
--entry-closure`, closure-loaded sources) trips inside
`parse_full_frontend`/the driver's phase-2 parse step. Not investigated
further — out of scope for the spin-hang task that uncovered it.

This is consistent with native-build already being documented as failing
100% of the time at baseline (0/15 in `native-smoke-matrix.shs`) behind a
different wall (`unknown extern function: rt_array_len_safe`, per commit
`60d2474620327551297c1412fbf361ecd0da0db3`) — native-build has multiple
sequential walls; this is simply the next one, now reachable because the
closure-hang wall in front of it is fixed.

## Repro

Same command as above, on this worktree's HEAD after the entry-closure O(n²)
fix lands. Add `SIMPLE_COMPILER_PHASE_PROFILE=1` to see the phase trace.

## Next steps (not done here)

- Bisect which part of `parse_full_frontend` (or a downstream semantic step
  invoked from the phase-2 loop) treats an array `Value` as an int.
- Check whether this reproduces with a *single* `--source` root (no
  entry-closure) to isolate whether it's closure-specific state (e.g.
  `options.input_files` / `bootstrap_input_count` overflow past the 6-slot
  `bootstrap_input_0..5` fields once >6 explicit inputs are pushed via
  `cli_native_build_add_bootstrap_input`) or general.
