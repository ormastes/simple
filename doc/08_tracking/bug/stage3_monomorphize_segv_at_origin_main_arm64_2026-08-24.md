# Stage 3 at `origin/main` clears HIR entirely and dies at `phase4:monomorphize` (arm64-darwin, 2026-08-24)

## What was run

Sanctioned lane only, in an isolated clean `git worktree --detach` at
`origin/main` `ee98a2c3222` — never the shared working tree.

```
# Stage 2 (the sole receipt-free lane)
bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 --output=<wt>/build/bootstrap
  -> "Stage 2 admitted; stopping before Stage 3 as requested."
     stage2 sha256 1db26649ff88eeb99dd89caef716f5491625c1fde3c286021b3bf86fda8ab752
     stage2-provenance.receipt + stage2-sanity.receipt written

# Stage 3 admission
bootstrap-from-scratch.sh planner-admission-v2 --target=//bootstrap:stage3 \
    --reason=seed-missing --parent-compiler=<stage2> --bootstrap-output=<wt>/build/bootstrap
  -> bootstrap-admission: produced .../planner-admission-v2.env

# Stage 3
bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/bootstrap \
    --bootstrap-receipt=.../planner-admission-v2.env
```

Two invocation facts worth recording, both cost a cycle:

* the receipt to pass is the **29-field `planner-admission-v2.env`**, not the
  one-line `authorization.receipt` — the latter is rejected as
  `planner-admission-v2-unbound` / `malformed-or-untrusted-planner-admission-v2`;
* `--resume-stage3-from-admitted` requires a **repo-relative** output path
  (`build/bootstrap`). An absolute path yields
  `ERROR — nothing was checked (OUTPUT_DIR must be a repo-relative path without .. components: ...)`.

The isolated worktree was the right call: Stage 3's git-state gate recorded
`git-state-before.env` == `git-state-after.env`
(`head=ee98a2c3222…`, `dirty_fingerprint=225b134c…` on both sides), so the gate
that silently fail-closes on a moving tree was satisfied. Both cache-scope
ownership gates passed:
`PASS — 1 marker checked, .../stage2-native-cache owned by lane 'stage2'` and
the same for `stage3`.

## Result: SIGSEGV at `phase4:monomorphize`, no artifact

```
[BOOTSTRAP-PHASE] +517800ms phase3:hir_typecheck:done
[build] hir unknown/unknown step 3/6 +517800ms dt=0ms complete
[BOOTSTRAP-PHASE] +517800ms phase4:monomorphize:start
[build] monomorphize 0/unknown step 3/6 +517800ms dt=0ms start
[build] monomorphize 0/unknown step 3/6 +517800ms dt=0ms specialize
.../scripts/check/lib/bootstrap-stage3/command-snapshot.shs: line 182:
  69697 Segmentation fault: 11   env -i "HOME=..." "PATH=..." ... exec "$@"
```

No `stage3/aarch64-apple-darwin/simple`, no `provenance.env`, no `full/`.
**Stage 4, Stage 5 and any deployment are therefore unreachable.** Nothing was
deployed.

## The frontend is now CLEAN — this is forward progress over RUN 9

Measured in the same log:

| | RUN 9 (`stage3_hir_imports_memory_explosion_...`, at `cde14a`-era) | this run (`origin/main`) |
|---|---|---|
| outcome | rc=1 on HIR semantic errors | SIGSEGV at monomorphize |
| `HIR lowering error` lines | present, blocking | **0** |
| `hir_finalize` | — | **947/947** |
| `post_hir_validate` | — | **692/692** |
| `unresolved type` | 761 over 295 modules, then ~2050 over ~590 | **427 over 692 modules** |
| furthest phase | `phase3:hir_typecheck` | `phase3:hir_typecheck:done`, then `phase4` |

The remaining 427 `unresolved type` lines are non-fatal and are dominated by
generic builtins — `Option` 151, `Result` 103, `Dict` 98, `fn` 8, `HirType` 5,
`T` 2, `Span` 2, `HirSymbol` 2. The `driver_riscv_gen2_product`
field-visibility set and the large `MethodResolution` population that blocked
RUN 9 are **absent**. So the HIR-side commits in the 96-commit range
(`430d5ac431d`, `4217e91e327`, `0560611bd6b`, `4558514d53f`) did move the
chain: the blocker is now a different, later one.

## Crash attribution — CORROBORATED, NOT first-party

**No backtrace was obtained for this run**, and no claim is made that it is
byte-identical to the known signature. Two honest limits:

1. **No crash report was written.** The compiler runs inside
   `command-snapshot.shs`'s `env -i` sandbox; no `.ips` appeared in
   `~/Library/Logs/DiagnosticReports` after the 17:54 fault.
2. **An lldb replay of the same argv was NOT faithful and is discarded.**
   Re-running the exact `native-build` argv from
   `stage3-command.transcript` outside that sandbox (notably without
   `SIMPLE_BINARY` and with a different `HOME`/`TMPDIR`/`PATH`) **exited 1 on
   HIR lowering errors instead of crashing** — `unresolved name` in
   `types/_TypeLayout/arch_and_verify.spl` and `ambiguous explicit callable
   dependency` in `hir_lowering/expressions.spl`. The real run had **0** such
   errors, which proves the replay diverged before it could reach monomorphize.
   It is recorded here as a negative result, not as evidence about the crash.

What corroborates the attribution, clearly labelled as someone else's run: the
most recent `simple` crash report on this host, `2026-08-24 13:08`, from an
earlier lane, is

```
exception: EXC_BAD_ACCESS / SIGSEGV, KERN_INVALID_ADDRESS at 0xf198715900000000
  simple 0x1fb56c compiler__mono__monomorphize__type_subst__substitute_stmt + 1520
```

Same phase, same binary family, and `0xf19871590000_0000` is a 32-bit value
sitting in the HIGH half of a 64-bit slot — the mirror image of the Stage-2
`hc_enc_hir_module` truncation recorded in
`stage2_hir_codec_segv_is_i32_truncated_heap_ref_2026-08-24.md`, where a 64-bit
heap pointer loses its high half. Both are width defects on a tagged word. That
is a **hypothesis with a stated mechanism**, not a measurement of this run.

## Reproduction cost

Stage 2 from cold: ~27 min wall (seed ~4 min + `750 compiled, 0 cached`,
1035 s compile + 17 s link). Stage 3 to the fault: ~518 s. Both on a 10-core
M-series with `--jobs` defaulting to 5. `build/` in the worktree is 3.8 GB.

## Not verified

* Any Stage 4 / Stage 5 / MCP behaviour. No stage-3 artifact exists, so none of
  it was reachable and none of it was attempted.
* Whether fixing the Stage-2 `hc_enc_hir_module` truncation would clear this.
* The `--no-mcp` fallback was **never** used, because Stage 5 was never reached.
