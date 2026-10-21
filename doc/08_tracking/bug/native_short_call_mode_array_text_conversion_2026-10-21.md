# Native short-call mode text conversion — 2026-10-21

## Symptom

The third call-loan native probe compiled, then segfaulted in
`__GI_strcmp` → `rt_text_eq_any` →
`NLLChecker.check_short_call` (exit 139 under the timeout guard). The captured
GDB snapshot is `build/nogc-hardening/mir_call_loans-text-crash-3.log`.

## Source and disassembly evidence

`src/compiler/55.borrow/borrow_check/nll_short_calls.spl`,
`NLLChecker.check_short_call`, reads a mode from the declared `[text]` vector
using an unannotated conditional expression:

```simple
val mode = if index < modes.len(): modes[index] else: "unknown"
```

The final probe binary disassembly shows the mode path calling `rt_array_get`
for `modes[index]`, then `rt_interp_cstr`, while the else branch constructs the
`"unknown"` literal. The merged value is passed to `rt_text_eq_any`. GDB records
the first comparison argument as `0x5555555dc6e88`, which is not a valid text
address in this process; the second argument is the valid literal pointer
`0xaaaaaabbe900`. The fault therefore localizes to the mode array item/result
conversion or branch merge. The `LoanEvent.ShortCall(arguments, modes)`
declaration and constructor both use `[Place]` then `[text]`, so this trace does
not indicate a record-field order mismatch.

## Candidate source change and status

The local candidate annotates the binding as `val mode: text = ...`, matching
the parameter's declared `[text]` element type. This is a narrow source-level
type constraint for the branch result. It remains unverified because the
three-cycle native qualification cap has been reached; no compiler or runtime
fix is claimed.

## Attempt four: downstream annotation did not fix the producer

The explicit mode binding annotation compiled but the current native call probe still segfaulted (exit 139, under one second); build succeeded in 272.93s, maximum RSS 6,726,340 KiB. Bounded disassembly and GDB localized an earlier producer: `BorrowChecker.record_short_call_contract` indexed its effect array through `rt_array_get` then `rt_value_as_int_wide`, and pushed through `rt_value_int_wide`. The resulting modes array already contained invalid derived text words before `LoanEvent.ShortCall`. Runtime capture showed both slots `0x0005555555dcee88`.

The next source candidate introduces formal `[text]`/`text` lookup and append boundaries in `borrow_check/mod.spl`; it changes no contract policy. Attempt five uses the existing cache and is running. No successful fix or acceptance result is claimed until its guarded run terminates.

## Attempt six: focused regression passes

Additional GDB/disassembly on attempt five showed the callee-name payload in `MirConstValue.Str(name)` was passed through `rt_value_int_wide` for dictionary contains/get; a valid text key therefore missed the checked-contract table. A formal `Dict<text,[text]>`/`text` lookup helper now preserves that key, alongside the typed mode lookup/append boundaries.

Attempt six compiled successfully in 275.33s (maximum RSS 7,596,976 KiB), then its exit-backed actual-MIR call corpus exited zero. Valid shared forwarding passed; conflicting/mutable aliases, boundary widening, absent/consuming/stale contracts, and escaping call-result provenance rejected as expected. Logs: `build/nogc-hardening/mir_call_loans-feature-build-6.log` and `mir_call_loans-feature-run-6.log`. This qualifies the focused source workaround, not a repaired/rebuilt r17 producer or full BOR-03/BOR-04 acceptance.
