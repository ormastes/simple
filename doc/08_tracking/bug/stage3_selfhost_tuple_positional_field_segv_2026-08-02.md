# Stage 3 self-host blocked — ADJUDICATED 2026-08-02: the tuple SEGV is not the cause

- **Status:** RESOLVED — root cause was a bootstrap-script bug, fixed in
  `scripts/bootstrap/bootstrap-from-scratch.sh`. The original title of this bug
  ("pure-Simple compiler SEGVs on tuple positional field access") is **REFUTED
  as an independent defect**; see "Adjudication" below.
- **Found:** 2026-08-02, full bootstrap lane at origin `da6cac2b6a3`
- **Adjudicated:** 2026-08-02 at origin `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`
- **Severity:** was blocker — stopped Stage 3 self-host
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh` (Stage 3 argv)

## Adjudication (2026-08-02)

Two lanes independently reached different "PROVED" root causes for the same
Stage-3 failure:

- **A (2026-08-01) — script bug.** Stage 3 invoked `native-build` without the
  `--source src/compiler --source src/app --source src/lib` roots and without
  `--entry-closure` that Stage 2 (and six other `native-build` call sites) pass.
- **B (2026-08-02) — compiler defect.** This document's original body: the
  pure-Simple compiler SEGVs on tuple positional field access.

**A is correct and sufficient. B is refuted.** B's SEGV is a real observation
but it is a downstream symptom of the *same* missing `--source` roots, it is
not tuple-specific, and it is off the Stage-3 path.

### Distinguishing test (PROVED)

Base sha `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`, extracted with
`git archive` into an isolated tree (shared working copy untouched). The
Stage-3 `native-build` was replayed verbatim from
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
against the admitted Stage-2 compiler, changing one variable at a time.

| variant | extra argv | result |
|---|---|---|
| baseline (current script) | none | **RC=1**, 441,951 log lines, **3,286** `unresolved type:` errors, no binary |
| A's fix | `--source src/compiler --source src/app --source src/lib --entry-closure` | **RC=0** — `727 compiled, 0 cached, 0 failed`, 127,670,776-byte binary, 663.7 s |
| roots only | `--source ...` without `--entry-closure` | not viable — 32.6 GB RSS after 33 min with no progress output; killed. `--entry-closure` is required for closure pruning. |

Stage-3 output binary, both identity gates (PROVED): size 127,670,776 B and
`strings <bin> | grep -c "enum construction: unregistered enum"` = **2**
(self-hosted, not the Rust seed); `--version` = `simple-bootstrap 1.0.0-beta`.

The failing baseline reproduces the prior full run exactly: that run's
`stage3-native-build.log` (12.7 MB, 2026-08-01 23:14) contains 3,344
`unresolved type:` + 546 `unresolved name:` diagnostics — diagnosis A's
predicted signature.

### Corrections to the claims previously recorded here

1. **The error message quoted below is not in the failing Stage-3 log.**
   `missing parsed module for source: std.nogc_sync_mut.io.process_governor`
   does **not** appear in
   `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
   (2026-08-01 23:14): 0 occurrences of `missing parsed module`,
   `process_governor` and `signal_stubs`. The single `[ERROR] phase 3 FAILED`
   line there sits in the middle of the `unresolved type` cascade.

2. **The SEGV is not tuple-specific.** A plain array index crashes at the
   identical PC:

   ```
   fn main():
       var a: [i64] = [1, 2]
       val x = a[0]
   ```

   Tuples reach it because `t.0` lowers to `Index(base, IntLit(i))`, not
   `TupleIndex` — see `src/compiler/20.hir/hir_lowering/expressions.spl:1381`
   ("expr_dispatch.spl has no TupleIndex case at all"). Family enumerated, all
   RC=139 on the misconfigured invocation: `t.0`, `t.1`, `t.2`, tuple in `val`,
   tuple as a parameter, nested tuple `((1,2),3).0`, tuple field off a call
   result `mk().0`, and array `a[0]`.

3. **The SEGV is an artifact of the missing `--source` root.** Same compiler,
   same source file, one variable:

   | invocation | result |
   |---|---|
   | `native-build f.spl` | **RC=139 SIGSEGV** |
   | `native-build --entry-closure f.spl` | **RC=139 SIGSEGV** |
   | `native-build --source pk f.spl` | **RC=0**, 0.3 s compile |

   With the root present the same programs compile and run correctly. Value
   check against hand-computed expectations (`t=(7,9)`, `arr=[11,22,33]`,
   `n=((1,2),3)`, `take(t) -> t.1`): printed `a=7 b=9 c=33 d=3 e=4` — all
   correct, and three of five differ from the nil sentinel `3`, so this is not
   a constant-3 artifact.

   A no-tuple, no-index `print("hi")` program fails on the same misconfigured
   invocation with `AOT compile error: <invalid-heap:0x...>`, further evidence
   that the fault is loader state and not tuple lowering. B's negative control
   (`val a = entry`, "no crash") was therefore too weak: it distinguished
   crash-vs-not, but not tuple-vs-any-index, and not compiler-vs-invocation.

4. **Not a stale-binary artifact.** The SEGV reproduces identically on a
   freshly built Stage-3 binary produced from this base sha, and disappears on
   that same binary once `--source` is supplied.

## Root cause and fix

`scripts/bootstrap/bootstrap-from-scratch.sh`, Stage-3 `native-build`
invocation — added, mirroring Stage 2 verbatim:

```
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
```

before `--threads "${selfhost_jobs}"`. Mechanism: the loader fills
`module_surfaces` from the transitive `use` closure only, so directory-package
siblings that nothing explicitly imports are never loaded and
`resolve_package_sibling_symbols`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) has nothing to
register — producing the `unresolved type` cascade.

`--entry` was deliberately NOT added: it reroutes to the Rust runtime and would
void the self-host evidence. Stage 3 keeps its bare positional
`src/app/cli/bootstrap_main.spl`.

## Still open — recorded, deliberately not papered over

**The compiler SIGSEGVs instead of emitting a diagnostic when package-sibling
symbols are unresolvable.** Crash site, PROVED by gdb against both the admitted
Stage-2 binary and the freshly built Stage-3 binary (identical PC):

```
0x54fbe8 <MirLowering.lower_dict_runtime_read+1048>: mov (%rbx),%rdi   ; rbx = 0
   +1025: call rt_native_neq        ; rsi = 3  (the nil sentinel)
   +1039: mov 0x8(%rsp),%rbx
   +1044: and $0xfffffffffffffff8,%rbx
```

A `!= nil` guard passes and the very next dereference is NULL — consistent with
a raw NULL (`0`) reaching a slot whose emptiness is encoded as the tagged nil
sentinel `3`, so `0 != 3` is true. Source region:
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:832-833`
(`if not resolved_from_local and base.has_type_ == true and base.type_ != nil:`
then `match base.type_.kind:`). This is a robustness defect (fail hard instead
of diagnose), not a self-host blocker: it is reachable only through a
`native-build` invocation missing its `--source` roots. It needs a real
NULL-vs-nil-sentinel discrimination fix, not a local guard patch, so it is left
open rather than covered up.

Observed on the same misconfigured path and also left open: `--source`-less
`native-build` of a dict read (`d["k"]`) or a struct field read (`p.x`) HANGS
(killed at 900 s) instead of crashing or completing.

The secondary fail-open diagnostic noted in the original report
(`src/compiler/20.hir/hir_lowering/module_surface.spl:379`,
`missing parsed module for source: ...` with no underlying cause) remains a
valid, separate improvement request.

---

## Original report (2026-08-02, superseded by the adjudication above)

Kept verbatim for provenance; items 1-4 above correct it.

### Symptom as seen by the bootstrap

`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=llvm --full-cli`

```
Stage 2: seed -> bootstrap_main.spl                 OK (727 compiled, 0 failed)
  Stage 2: running bootstrap compiler sanity        OK
  Stage 2 native-build capability passed            OK
Stage 3: stage2 -> bootstrap_main.spl (self-host)   FAILED (exit 1)
```

Reported log excerpt:

```
[ERROR] phase 3 FAILED
error: in-process native-build: Module surface extraction error:
       missing parsed module for source: std.nogc_sync_mut.io.process_governor
```

### Reported root cause (refuted)

1. Compiling `src/lib/nogc_sync_mut/io/process_governor.spl` reports
   `missing parsed module for source: std.nogc_sync_mut.io.signal_stubs`.
2. Compiling `src/lib/nogc_sync_mut/io/signal_stubs.spl` directly segfaults
   (rc=139) during MIR lowering. `signal_stubs.spl:29-30` is
   `val sig = entry.0` / `val cb = entry.1`.

| probe | body | result |
|-------|------|--------|
| `val entry = (7, 8)` then `val a = entry`   | whole tuple | no crash |
| `val entry = (7, 8)` then `val a = entry.0` | field 0 | rc=139 SIGSEGV |
| `val entry = (7, 8)` then `val a = entry.1` | field 1 | rc=139 SIGSEGV |

### Relationship to prior state (as reported)

The 2026-07-31 verdict (`project_stage3_selfhost_blocked_2026-07-31`) is stale
and was measuring a different blocker: on 2026-07-31 Stage 3 *succeeded*
(727 compiled, 124.5 MB stage3 binary linked) and Stage 4 was the blocker, with
a parse error in `src/compiler/20.hir/hir_lowering/expressions.spl`.

The suggested link to the porter regression fixed in `284745a3cfc` /
`28adeb80809` (mis-rewriting `x.0` into `x[0]`) was inferred, never bisected,
and is now superseded: the crash is not tuple-specific at all.
