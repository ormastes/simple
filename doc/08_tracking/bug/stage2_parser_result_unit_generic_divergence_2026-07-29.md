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
The file itself (`vhdl_codegen_helpers.spl`) is an in-flight working-copy
file (not on origin/main as of 38cb691ad082), so origin is currently
bootstrappable — but the moment such code lands, stage 3 breaks. Per repo
rule ("when a short, safe grammar form fails, fix it or record a concrete
bug"), this needs the pure-Simple parser (src/compiler/10.frontend) to accept
unit `()` as a generic type argument, with a spec locking both parsers.

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
