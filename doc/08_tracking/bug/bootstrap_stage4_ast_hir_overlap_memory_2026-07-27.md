# Bootstrap Stage 4 AST/HIR overlap exhausts the no-GC heap registry

## Status

Open. The full `src/app/cli/main.spl` Stage 4 closure still does not produce a
native executable on the 4 GiB-class Linux development host.

## Reproduction

Run the Stage 3 compiler with `SIMPLE_BOOTSTRAP_STAGE4=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, `--entry-closure`, `--low-memory`, one thread, and
the `src/compiler`, `src/app`, `src/lib`, and `examples/10_tooling` source roots.
The closure contains about 1,303 unique modules.

Evidence is retained under:

- `build/mini_builds/stage4_retry21.log`
- `build/native_probe/stage4_retry21.time`

## Observed

- Original peak RSS: about 6.1 GiB, terminated by OOM.
- After closure/cache and frontend-memory fixes: about 3.0–3.7 GiB.
- After reusing one pre-registered HIR diagnostic buffer: 2,812,760 KiB.
- The remaining failure is `runtime error: field access on nil receiver` after
  the terminal `future.spl` HIR module returns and before diagnostic collection
  completes.
- Earlier phase tracing measured about 21.85 million registered heap objects at
  the terminal HIR module.

## Root cause

The low-memory pipeline releases raw source contents after parsing and clears
the AST dictionary after HIR, but peak memory occurs during HIR. At that point
all parsed `Module` ASTs, accumulated `HirModule` values, and the flat bootstrap
HIR store are live together. The core-C bootstrap runtime has no tracing GC;
most dictionaries, enums, closures, strings, and conversion-created arrays
remain allocated/registered after Simple references are dropped.

The C array registry also ignores registry-growth allocation failure and can
return an unregistered heap handle. That is a correctness bug, but correcting
it alone only turns the memory failure into an explicit allocation failure.

## Implemented mitigation

The driver now allocates one typed `[LoweringError]` buffer before the HIR loop,
passes it into a dedicated `HirLowering` factory, projects diagnostics through
owner methods, and clears/reuses the same registered handle. This reduced the
measured peak by roughly 300–800 MiB without changing diagnostics.

The diagnostic projection is now flat and span-free (`[text]` plus `[bool]`),
avoiding the bootstrap ABI failure when a nested `Span` is extracted from an
array-held `LoweringError`. Stage 4 subsequently completed HIR collection
instead of trapping on the terminal `future.spl` module.

Phase 2 retains all logical aliases in `modules_by_name`, but now passes only
its unique physical source list into Phase 3. On the full CLI closure this
removed 420 duplicate HIR lowerings (1723 aliases versus 1303 files), reduced
diagnostics from 6132 to 5206, and reduced peak RSS from 4,059,988 KiB to
3,493,940 KiB.

HIR glob registration now expands one hop through declaration-empty facade
modules and resolves their explicit export lists. The bounded version reduced
the next diagnostic set from 5206 to 2315 and eliminated the dominant
`MirType`/`MirTypeKind` family. An earlier unrestricted depth-8 expansion is
rejected evidence: it was killed at 6,169,364 KiB. The bounded run completed
Phase 3 diagnostic collection at 4,352,600 KiB.

Subsequent source-accurate fixes added the omitted MIR operand re-exports,
completed the lexer scanner's selective helper import, accepted `me` as an
alias of the canonical `self` HIR receiver, exported split parser AST types,
and corrected MIR optimization imports. Diagnostics fell from 2315 to 1212
with a 3,769,480 KiB peak, then to 722 with a 4,291,316 KiB peak. The remaining
largest families are explicit re-export/type-alias facades (`T32BridgeResult`,
`FixConfidence`, `Replacement`, `EasyFix`) rather than the original memory or
nested-diagnostic crash.

## Required structural fix

Introduce a two-pass, streaming HIR pipeline using `ModuleSurface` as compact
cross-module authority:

1. Parse/extract imports, signatures, composites, enums, constants, traits,
   impl signatures, aliases, and required trait default bodies.
2. Reparse or retain one module body at a time.
3. Lower it against module surfaces.
4. Publish its flat-HIR record and release its AST/body before advancing.

Tests must cover glob imports, aliases, imported enum variants, trait defaults,
impl signatures, deterministic closure order, and entry-closure output parity.

## Acceptance

- Full Stage 4/4b/5 bootstrap completes on the target PC.
- Peak RSS remains below the host limit with `SIMPLE_NO_STUB_FALLBACK=1`.
- The deployed `bin/simple` builds and runs a representative program.
- No generic/diagnostic errors are suppressed to obtain the binary.
