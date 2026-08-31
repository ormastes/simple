# Freestanding riscv64: module-level ARRAY globals are never initialized

Date: 2026-08-31
Status: OPEN — root cause measured in-guest, not yet fixed
Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
Probe: `examples/09_embedded/simple_os/arch/riscv64/text_primitive_probe_entry.spl`
       via `scripts/check/run-riscv64-text-probe-opensbi.shs` (real OpenSBI
       v1.4 `-bios fw_payload`; never `-kernel`, never `isa-debug-exit`)

## Statement

In a freestanding riscv64 native build, a module-level global declared with an
ARRAY LITERAL initializer — `var g: [T] = [...]` — is **not initialized**. The
array reads back with the wrong length, every element read yields
empty/nil, and every element store into it is lost. Module-level SCALAR globals
(both `text` and `i64`) initialize and persist correctly, in the same image, in
the same run.

This is a codegen/global-initializer defect. It is **not** a missing runtime
symbol and **not** a text-primitive defect.

## Evidence — one boot, real firmware

    [probe] 12a plain text global = GLOBAL_OK        <- scalar text global: OK
    [probe] 12c i64 global = EXPECTED                <- scalar i64 global: OK
    [probe] 12d read via fn = GLOBAL_OK              <- scalar, read in another fn: OK

    [probe] 12b [text] slot global =                 <- [text] global slot: EMPTY
    [probe] 14a i64 slot = WRONG                     <- [i64] global slot: WRONG
    [probe] 14b same-fn = <empty>                    <- write+read in ONE fn: still lost
    [probe] 14c re-read of the 12b slot = <empty>
    [probe] 14c 12b slot len = WRONG                 <- the LENGTH is wrong, not just the element

Declarations under test:

    var g_probe_text: text = ""          -> works
    var g_probe_num: i64 = 0             -> works
    var g_probe_text_slot: [text] = [""] -> length wrong, element store lost
    var g_probe_num_slot: [i64]  = [0]   -> length wrong, element store lost

`14a` is the load-bearing one: the element type is `i64`, so this is **not**
text-specific. `14b` rules out the function boundary: the write and the read are
in the same function and the value is still lost. `14c` rules out "not yet
written": the array's own `len()` is wrong, so the initializer never ran.

## Why this is Defect A of the riscv64 in-guest interpreter lane

Both rows of that lane fail identically:

    [stderr] [parser-module] decl:start i=0 kind=3 text= line=3 col=3
    [parser_error] line 3:3: parser made no forward progress at this token
                   (StringLit ''); aborting module parse
    [parser_error_ctx] path  kind 3 text ''

`src/compiler/10.frontend/core/lexer_struct.spl` stores the current token in
exactly this shape:

    var core_last_token_text_slot: [text] = [""]
    var core_last_token_line_slot: [i64] = [0]
    var core_last_token_col_slot: [i64] = [0]
    var core_last_token_suffix_slot: [text] = [""]
    var core_token_env_save_slot: [bool] = [false]

Every one of those is a module-level array-literal global, and
`core_token_capture` writes the token through them. Under this defect they are
uninitialized, so the captured token text is lost while the token KIND — which
the lexer keeps in `self.cur_kind` on the lexer struct, not in a global slot —
survives. That is precisely the observed signature.

## Hypotheses DISPROVED on the way here (all measured in-guest, same probe)

* **`rt_slice` raw-vs-tagged indices.** The aarch64 divide-by-8 fix
  (`6c57b45105c`) is already in this base and riscv64's `rt_slice` takes RAW
  indices. `substring(0,6)`, `substring(1,5)`, `substring(8)`, `chars()`
  indexing, `trim`, `starts_with`, equality and a bounded json_find scan are all
  correct in-guest.
* **The `[text]` push + `join("")` accumulator** that `scan_string` builds token
  text with. Probe step 10: `10a join = abc`, `10b join = a-b-c`,
  `10c join = "use` — all correct. LOCAL arrays are fine; only MODULE-LEVEL
  array globals are broken.
* **Struct-method `advance()` + `while true:` loop-carried local** (step 11):
  `11 join = abcd`, correct.
* **Flat-Optional decode** (step 13), the lead from the parallel `to_int()`
  lane: `"2".to_int() ?? 0` and `"4242".to_int() ?? 0` both EXPECTED in-guest,
  and `Optional<text>` present/absent both decode correctly. That lane's
  `to_int()` defect is real but is **not** this one — reported as a
  disagreement, not silently dropped.

## Next step

Fix global array-literal initializer emission for the freestanding target. Note
that some call sites already carry a defensive repair
(`if slot.len() == 0: slot = [""]`) — whether a whole-array assignment to a
global persists in-guest is NOT yet measured and should be the first thing the
fix's probe checks, because if it does, that repair path is a possible route
around while the codegen fix lands.
