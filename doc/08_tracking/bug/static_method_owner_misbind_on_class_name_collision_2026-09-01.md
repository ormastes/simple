# Static-method owner MISBIND when two classes share a NAME (exact_symbols textual key collision)

Date: 2026-09-01. Status: OPEN (structural; pre-existing seat, newly reachable silently).

## Repro (measured)

    # dup_a.spl                      # dup_b.spl
    class Dup:                       class Dup:
        tag: text                        tag: text
    impl Dup:                        impl Dup:
        static fn new() -> Dup:          static fn new() -> Dup:
            Dup(tag: "A")                    Dup(tag: "B")

    # main_dup.spl
    use app.zz.dup_a.{Dup}
    use app.zz.dup_b.{Dup as DupB}
    fn main():
        val d = Dup.new()
        print "dup tag={d.tag}"      # interpreter: tag=A (correct)
                                     # native build: tag=B (WRONG, silent)

Before the cross-module static-new fix this case errored loudly (rc=1, "undefined variable
Dup"); the interpreter has always printed A. After the fix the native build succeeds and
silently constructs the WRONG class.

## Mechanism

The misbind is NOT in the new recovery's owner choice -- the attached symbol id is correct
(`SymbolTable.define` is first-write-wins for type symbols, so `Dup` = dup_a's id 0;
traced: `attached_id=0 owner_id=0`). It is in the METHOD key:
`method_symbol_name_raw` (`hir_symbol_table_methods.spl:279`) builds
`"{defining_module}.{TypeName}::{method}"` but falls back to bare `"TypeName::method"`
when the type symbol's `defining_module` is empty -- which it is on this lane -- and
`exact_symbols` is last-write-wins, so dup_b's `new` overwrites dup_a's under the SAME
`"Dup::new"` key. Every textual-key consumer (`lookup_method_in_type`,
`lookup_static_method`, the name-derived recovery at method_calls_literals.spl:2937)
inherits this; instance methods of same-named classes are exposed to the same clobber.

The tree has hundreds of duplicated class names across `src/` (e.g. `Actor`,
`AdapterConfig`, ...), so closures that pull two same-named classes with same-named
methods are realistic.

## Proper fix (not attempted here -- silently-wrong-values hazard demands care)

Either populate `defining_module` for type symbols on the native whole-program lane so the
qualified keys never collide, or key method registration by owner SYMBOL ID instead of
text, or track an ambiguity bit at define-time so lookups can fail closed. Wrong scope
for the MIR-layer change that exposed it; needs its own lane.
