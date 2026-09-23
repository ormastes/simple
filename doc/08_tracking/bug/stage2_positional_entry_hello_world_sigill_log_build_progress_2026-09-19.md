# Stage 2 candidate SIGILLs (rc=132) in the hello-world POSITIONAL-entry smoke

Date: 2026-09-19
Status: OPEN — blocks Stage 2 admission since attempt 46 of the
`work/image-memory-budget-20260915` bootstrap campaign. Cache-corruption
hypothesis REFUTED (see Attempt 48). Not yet root-caused.
Lane: bootstrap chain, Windows 11 Git Bash host, Xeon W-2135, 15.7 GB RAM.

## Symptom

`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
--backend=cranelift` builds the Stage-2 candidate fine (8 compiled, 876
cached, 0 failed, 141 s warm; identical result cold), then the sanity smoke
dies at the LAST probe:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)
```

rc = 132 = 128 + SIGILL. The candidate prints exactly one progress line and
traps inside `log_build_progress`:

```
[build] phase=load_sources state=running unit_kind=files done=unknown
total=unknown remaining=unknown succeeded=unknown cached=0 failed=0
task_done=0 task_total=6 elapsed_ms=0 dt_ms=0 current=starting
```

Probes 1-3 of the same smoke (`p2_add.spl`, `stage2_mir_retention.spl`,
`stage2_module_path_naming.spl`, all invoked with the `--entry` FLAG) PASS
with the same candidate binary. Only the POSITIONAL entry form
(`native-build ... fixtures/hello_world.spl --output ...`) traps.

## Exact repro (preserved candidate: /tmp/stage2-candidate.exe, 65,601,059 bytes)

```sh
export SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
  SIMPLE_BINARY=$C SIMPLE_BIN=$C SIMPLE_BOOTSTRAP_DRIVER=$C \
  SIMPLE_FRONTEND_DELEGATE=$C SIMPLE_FRONTEND_DELEGATED=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_EXECUTION_MODE= \
  SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 SIMPLE_BOOTSTRAP=0 SIMPLE_LIB=$PWD/src
"$C" native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry-closure --cache-dir <fresh> --mode one-binary \
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output <out>
# C=candidate: raw rc=132 (SIGILL)
# C=bin/simple.exe (Rust seed): blocked earlier at the SCV freeze
#   (SCV-E-SNAPSHOT: snapshot-inventory-empty, rc=1) — different env contract,
#   so the seed never reaches the trapping path with this smoke env.
```

With `--entry scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
instead of the positional form: rc=0 SUCCESS (verified on the candidate).

Standalone gate agrees:
`sh scripts/check/check-stage2-hello-world-native-build.shs /tmp/stage2-candidate.exe`
traps in both arms (env-dependent flakiness SIGILL vs SIGSEGV).

## gdb evidence (deterministic)

Backtrace top:

```
#0 compiler.driver.driver_log_helpers.log_build_progress ()
```

`log_build_progress+2731` is a `ud2` ONE BYTE after the function's normal
`ret` (function base 0x1417581e0 in the preserved exe; ASLR base differs per
run). The basic block that falls into it:

```
+1401: call  *rt_println_value          ; the "[build] phase=..." print
+1410: call  *(unresolved flush fn)      ; rt_stdout_flush()
+1425: call  *rt_string_new_literal
+1446: call  *rt_string_data             ; rax = data pointer
+1449: test  %rax,%rax
+1452: jne   +2731 -> ud2                ; NONZERO data pointer TRAPS
```

Registers at the trap: rax=1, rbx=7, rcx=0, rdx=8324656, rsi/rdi = heap
pointers. So the candidate-compiled code holds an invariant "this
rt_string_data call must yield 0 (NULL) here, anything else is unreachable" —
in a correct program the check passes 0; on the positional path it sees
nonzero and hits `ud2`.

Source of the trapping function: `src/compiler/80.driver/driver_log_helpers.spl:258`
`log_build_progress` — print, `rt_stdout_flush()`, then
`if path == "": return`, then the events-file append tail. The function is
byte-identical to origin/main (last touched upstream e0fa5ef45e2).

## Why this is NOT cache corruption (Attempt 48)

Attempt 45's stage-2 build OOMed at 10,275 MB RSS ("memory allocation of
2953120 bytes failed") after writing 876 cache objects. Hypothesis: the
warm-cache candidate (attempt 46) inherited corrupt cache objects.

Attempt 48 moved `stage2-native-cache` aside to
`stage2-native-cache.oom-suspect` and rebuilt COLD from the admitted parent.
The cold-built candidate traps rc=132 at the identical site. The cache the
OOM-killed process wrote parses fine and reproduces identical results;
corruption refuted. (The `.oom-suspect` dir was deleted; the cache is
innocent.)

## Key structural clue: the function is not universally broken

The same candidate binary runs `log_build_progress` hundreds of times during
probes 1-3 (`--entry` builds) without trapping. The positional build traps on
its FIRST call, at phase=load_sources, current=starting. Two readings:

1. Context-specific miscompile: the positional path reaches the first
   progress call with different surrounding register/stack state, and a
   latent codegen defect in or around `log_build_progress` (missing spill,
   bad stack slot, wrong stack map) detonates on the invariant check above.
2. The trap is a downstream symptom: earlier positional-entry code (entry
   resolution before load_sources) corrupts state, and `log_build_progress`
   is merely where an invariant catches it.

The `jne ud2` checks `rt_string_data(...) != 0`; frame #1/#2 of the original
backtrace were runtime string-interning frames
(`STRING_LITERAL_INTERN` -> hashbrown `HashMap::insert`), consistent with
argument/entry interning on the positional path.

## Attempts log

- 45: stage-2 build OOM at 10.3 GB RSS (commit ceiling ~23.9 GB total
  virtual; co-session held 3.4 GB). Structural <7 GB work filed as follow-up.
- 46: warm-cache candidate built in 141 s (64 MB exe via g++) but the
  positional smoke trapped rc=132. A STALE sibling evidence log from
  Sep 15 initially misled the diagnosis harness (since fixed: stale
  evidence leaves are archived, "archived 11 stale evidence leaf(s)").
- 47: preserved the candidate exe; reproduced with the smoke's exact env;
  gdb localized the ud2; standalone gate confirms.
- 48: cold-cache rebuild — traps identically. Corruption hypothesis dead.

## Next steps

1. ~~Bisect the positional path~~ (superseded by attempt-49d evidence below).
2. Compare the candidate's codegen of `log_build_progress` against the
   seed's JIT output for the same function (symbol addresses differ; match
   by call sequence: rt_println_value -> flush -> string interning).
3. Workaround candidate (if the chain must move first): split the
   events-append tail of `log_build_progress` into its own function so the
   `if path == "": return` becomes the literal tail — changes codegen shape
   without changing behavior. Record here whether it dodges the trap; if it
   does, that narrows the defect to the tail's stack layout.
4. The preserved exe is at /tmp/stage2-candidate.exe (65,601,059 bytes);
   copy rule: only AFTER `Linked:` appears in stage2-native-build.log and
   size > 60 MB — copying at file-appearance yields 0 bytes (the wrapper
   deletes the binary on abort).

## Attempt 49 (2026-09-19) — workaround REFUTED

Committed e20afbca324: restructured `log_build_progress` so the early return
is `if path != "": _log_build_progress_event(...)` with the events-file
append in its own function — semantics identical, codegen shape changed
specifically to dodge an inverted/impossible early-return branch.

Attempt 49d (cold, after clearing two stale portable_lock files left by the
/tmp-purge-killed attempt 49 — see below) rebuilt stage 2 with the
restructured source and the positional smoke FAILED IDENTICALLY:
`candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)`,
same single progress line, same trap class. The early-return shape is NOT
the defective construct. The trapping invariant check (`rt_string_data`
result must be 0 after the print+flush sequence) is either genuinely in the
restructured function still, or the trap is a downstream symptom of state
corruption in the positional-entry driver path that runs BEFORE the first
progress call. Next diagnostic: bisect the pure-Simple driver path between
`native_build_single_spl_positional` entry and the first
`log_build_progress` call, and diff register/stack pressure against the
working `--entry` FFI path.

NOTE: /tmp/stage2-candidate.exe was lost in the 2026-09-19 /tmp purge; the
wrapper deletes the candidate on abort, so a fresh preservation requires a
successful stage2 link first.
