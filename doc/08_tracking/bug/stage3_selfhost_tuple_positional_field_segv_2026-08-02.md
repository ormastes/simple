# Stage 3 self-host blocked: pure-Simple compiler SEGVs on tuple positional field access

- **Status:** OPEN
- **Found:** 2026-08-02, full bootstrap lane at origin `da6cac2b6a3`
- **Severity:** blocker — stops Stage 3 self-host, so no Stage 4 full CLI, so
  `bin/simple` cannot be restored to a pure-Simple binary
- **Component:** pure-Simple compiler, tuple positional field lowering

## Symptom as seen by the bootstrap

`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=llvm --full-cli`

```
Stage 2: seed -> bootstrap_main.spl                 OK (727 compiled, 0 failed)
  Stage 2: running bootstrap compiler sanity        OK
  Stage 2 native-build capability passed            OK
Stage 3: stage2 -> bootstrap_main.spl (self-host)   FAILED (exit 1)
```

`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`:

```
[ERROR] phase 3 FAILED
error: in-process native-build: Module surface extraction error:
       missing parsed module for source: std.nogc_sync_mut.io.process_governor
```

The wrapper then correctly refuses to fall back to the seed:

```
Stage 3 unavailable — no provenance-verified compiler for Stage 4
error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback
```

## Root cause

The reported module is a red herring one level up. Narrowing with the Stage 2
binary (`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`):

1. Compiling `src/lib/nogc_sync_mut/io/process_governor.spl` reports
   `missing parsed module for source: std.nogc_sync_mut.io.signal_stubs`
   — i.e. its dependency, not itself.
2. Compiling `src/lib/nogc_sync_mut/io/signal_stubs.spl` directly
   **segfaults** (rc=139, core dumped) during MIR lowering.

`signal_stubs.spl:29-30` is:

```
        val sig = entry.0
        val cb = entry.1
```

Minimal reproduction against the Stage 2 pure-Simple compiler, with a negative
control that does NOT crash:

| probe | body | result |
|-------|------|--------|
| `val entry = (7, 8)` then `val a = entry`   | whole tuple | **no crash** (proceeds to llc) |
| `val entry = (7, 8)` then `val a = entry.0` | field 0 | **rc=139 SIGSEGV** |
| `val entry = (7, 8)` then `val a = entry.1` | field 1 | **rc=139 SIGSEGV** |

Reproduced 2/2 on repeat runs. Binding the whole tuple is fine; binding a
*positional field* of it segfaults. The Rust seed compiles the same file
without complaint, which is why Stage 2 passes and only Stage 3 — the stage
driven by the pure-Simple compiler — fails.

## Secondary defect: the diagnostic is fail-open

`src/compiler/20.hir/hir_lowering/module_surface.spl:379` emits

```
return Err("missing parsed module for source: {source.module_name}")
```

whenever a loaded `SourceFile` has no entry in the phase-2 `modules` dict. It
never says *why* the module is absent — a parse failure, a lowering crash, and
a module-name key mismatch are all reported identically, and here no
`[parser_error]` was printed at all. This message should carry the underlying
phase-2 failure, otherwise every diagnosis has to re-bisect by hand as above.

## Relationship to prior state

The 2026-07-31 verdict (`project_stage3_selfhost_blocked_2026-07-31`) is stale
and was measuring a different blocker: on 2026-07-31 Stage 3 *succeeded*
(727 compiled, 124.5 MB stage3 binary linked) and Stage 4 was the blocker, with
a parse error in `src/compiler/20.hir/hir_lowering/expressions.spl`. The
accumulated 2026-08-01 parser/HIR fixes moved the failure, and Stage 2 has its
own newly-surfaced blocker fixed separately in `da6cac2b6a3`
(`HmInferContext.accumulate_effect` undefined at link).

This defect is plausibly in the same family as the porter regression fixed in
`284745a3cfc` / `28adeb80809`, which mis-rewrote `x.0` into `x[0]`; tuple
positional field lowering is exactly the path both touch. That link is
**inferred, not proved** — it has not been bisected to a commit.

## Repro command

```
S2=build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
RT="$(pwd)/src/compiler_rust/target/bootstrap"
printf 'fn main():\n    val entry = (7, 8)\n    val a = entry.0\n    print("done")\n' > probe.spl
SIMPLE_BOOTSTRAP=1 SIMPLE_RUNTIME_PATH="$RT" $S2 compile probe.spl --format=smf -o probe.smf
# expect: rc=139, core dumped
```

Use a **relative** path — `simple compile` with an absolute path exits 0
without compiling.
