# Stage-3 parse failure in vhdl_codegen_helpers.spl (2026-07-29)

**Found:** L7 bootstrap run 4 (stage-3 self-host, cranelift dynload).
**Status:** RETRACTED diagnosis / no longer reproducible — see
"2026-07-30 retraction" below. The title's original claim
(`Result<(), E>` rejected) is DISPROVEN.

## 2026-07-30 retraction — measured against a real stage-2 binary

The two earlier diagnoses in this doc were both inferred from the error
text, never tested. Direct measurement disproves both. Method: parse
candidate constructs and the real victim file with an actual stage-2
pure-Simple binary
(`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build`),
which is the same parser stage 3 runs.

| Construct | Claim | Measured |
|---|---|---|
| `fn f() -> Result<(), text>:` | rejected | **parses clean, exit 0** |
| `match if c: a else: b:` (inline if as match subject) | rejected | **parses clean, exit 0** |
| `vhdl_codegen_helpers.spl` @38cb691ad082 (the pinned run-8 tree) | parse error at 207:135 | **zero parser_error**; reaches HIR |
| same file @110f743b2a2 (origin) | — | **zero parser_error**; byte-identical to the pin |

Reading the source confirms it: `parser_parse_type_impl` already handles a
parenthesized empty type group (`src/compiler/10.frontend/core/parser.spl`,
the `if par_kind_get() == 140` tuple branch → `TYPE_ANY` for a 0/1-element
group), so `Result<(), E>` was never a gap.

A whole-tree stage-2 `native-build` over current origin also reports
**zero `parser_error` and zero stale-generation/OOB diagnostics**.

So the run-4/run-8 parse error was NOT a property of that file or of either
construct. It only appeared in a whole-tree build, which points at
cross-file parser/lexer state rather than grammar — the same class as the
arena-generation work in L6. Do not "fix" the grammar or the victim file on
the strength of this doc.

**Process lesson:** every claim in the original write-up came from reading
an error message, and each one pattern-matched to a plausible grammar gap
that did not exist. Two separate agent lanes were nearly dispatched to fix
phantom bugs. Reproduce against the actual stage-2 binary before recording
a divergence — see memory `feedback_measure_the_primitive_before_building_on_a_derived_signal`.

## Original report (superseded — kept for the audit trail)

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
