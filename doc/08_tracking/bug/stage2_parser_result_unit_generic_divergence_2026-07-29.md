# Stage-2 pure-Simple parser rejects `Result<(), E>` the seed accepts (2026-07-29)

**Found:** L7 bootstrap run 4 (stage-3 self-host, cranelift dynload).
**Status:** Open — divergence recorded; not yet fixed.

## Symptom

Stage 3 fails in phase 2 with:

```
[parser_error] line 207:135: unexpected token in expression: ':'
[parser_error] path src/compiler/backend/backend/vhdl_codegen_helpers.spl
  line 208:9: expected :, got val 'val'
error: in-process native-build: parse error in .../vhdl_codegen_helpers.spl
```

Line 207 ends `... -> Result<(), CompileError>:` — the stage-2 (pure-Simple)
parser fails on the unit type `()` inside generic arguments, while the Rust
seed parses the same file fine (it authored/compiled it). 6 occurrences of
`Result<(), ...>` in that one file.

## Why this matters

Classic bootstrap divergence: code the seed accepts becomes un-self-hostable.
**CORRECTION (2026-07-30, L7 run 8):** the file IS on origin — tracked at
`src/compiler/70.backend/backend/vhdl_codegen_helpers.spl`; the earlier
"not on origin" verdict was a symlink-spelling miss (`src/compiler/backend`
→ `70.backend`, so `ls-tree` on the reported path returned nothing).
**origin/main is currently un-self-hostable**: a hermetic worktree bootstrap
(pinned 38cb691ad082, isolated build dir, clean status) reproduces the
stage-3 parse failure. Severity upgraded accordingly. Fix: the pure-Simple
parser (src/compiler/10.frontend) must accept unit `()` as a generic type
argument, with a spec locking both parsers.

## Repro

```
printf 'fn f() -> Result<(), text>:\n    Ok(())\n' > /tmp/p.spl
# seed parses; stage2 binary (build/bootstrap/stage2/<triple>/simple) errors
```

(Stage-2 binary lacks `run`; reproduce via its compile path or the full
bootstrap.)

## Also noted

`src/compiler/backend/backend/` is a symlink-spelling module path (see
memory: compiler symlink module spellings) — unrelated to the parse failure
but worth normalizing when the file lands.
