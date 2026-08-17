# `bin/simple compile` false-fails any main-less module with a module-level global

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
handle the same modules correctly, but single-file compile (the recommended
syntax/semantic gate) false-fails a large class of library modules.

## Symptom chain (2026-07-29)

Compiling `src/lib/nogc_sync_mut/io/font_sffi.spl`, `src/lib/scv/*.spl`, or
`src/lib/skia/feature/shaper/ot_layout_shaper.spl` fails:

```
semantic: <entry file>: Undefined("undefined identifier: _signal_handlers")
```

`_signal_handlers` is a module global of `src/lib/nogc_sync_mut/io/signal_stubs.spl`
(pulled in via the io graph) — declared at line 6, used only inside its own
module. The error is attributed to whatever entry file was compiled.

## Truth table (minimal repros, seed `bin/simple compile`)

| Module shape | Result |
|---|---|
| `var` global (any type: i64/text/[i64]/[(i64,fn())]) + fn that WRITES it, no `main` | `Undefined("undefined identifier: <global>")` |
| `var` global + fn that only READS it, no `main` | `SMF emission failed: the entry script could not be lowered to a real main entry point` |
| `val` global, no `main` | same SMF emission failure |
| ANY of the above + `fn main()` added | compiles clean |

Global type is irrelevant; presence of `main` is the discriminator.

## Mechanism

`compile` treats the input as an ENTRY SCRIPT. A module-level `var`/`val` is a
top-level statement, so the lane tries to synthesize a `main` from it:
- read-only/`val` case: synthesis fails loudly (the SMF emission error);
- written-global case: the synthesized-entry path drops the global's owner
  binding for function bodies, producing the misleading `undefined identifier`.

Sibling of the entry-module owner-bindings family fixed for `use` imports in
`0c53d0bdcc8` (stage4 memory-harden): markers/bindings only existed for
imported modules; here the entry module's OWN globals hit the same gap in the
compile lane.

## Impact

- Any module with a global — or importing one anywhere in its graph — cannot be
  single-file verified with `compile`. The io graph (`signal_stubs`,
  `signal_handlers`, `font_sffi`), scv, and the shaper entry are all blocked.
- Since `lint` passes files that do not parse, and `compile` false-fails this
  class, there is NO working single-file gate for these modules today.
  Workaround gate: `bin/simple compile` a small entry file with `fn main():`
  that imports the module under test.
- Errors are attributed to the entry file, not the global-bearing module,
  costing every investigator a graph walk (three separate lanes hit
  `_signal_handlers` this week before it was traced here).

## Repro

```
printf 'var _n: i64 = 0\nfn get() -> i64:\n    _n\n' > /tmp/g.spl
bin/simple compile /tmp/g.spl    # SMF emission failure
printf 'var _n: i64 = 0\nfn add():\n    _n = _n + 1\n' > /tmp/g2.spl
bin/simple compile /tmp/g2.spl   # Undefined("undefined identifier: _n")
```

## Fix direction

In the compile/SMF lane, detect module-shape files (only declarations at top
level) and compile them as LIBRARY modules — registering globals with owner
bindings exactly as the `run`/`native-build` lanes already do — instead of
forcing entry-script synthesis. The written-global `Undefined` should be
impossible once globals register; the SMF emission error should only remain
for genuine top-level executable statements.
