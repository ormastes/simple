# interpreter: step-slicing a `Value::StrBytes` hard-errors ("cannot slice value of type str with step")

Date: 2026-08-31
Status: FIXED (this session) — `Value::StrBytes` arm added in
`src/compiler_rust/compiler/src/interpreter/expr/collections.rs`

## Symptom

`error: semantic: invalid operation: cannot slice value of type str with step`
raised by the interpreted step-slice `Expr::Slice` handler, reported blocking
a one-line hello-world `native-build` on this checkout before parsing even
begins (sibling-agent reproduction). The message is misleading:
`StrBytes::type_name()` also returns `"str"`, so it reads as a `str` that
cannot be sliced, immediately below a working `Value::Str` arm.

## Root cause

`collections.rs`'s step-slice result match (`let result = match recv_val`)
had explicit arms for `Value::Array`, `Value::ByteArray`,
`Value::FrozenByteArray`, `Value::Str`, `Value::Tuple`, `Value::LabeledTuple`
— but no arm for `Value::StrBytes`, falling through to the generic `_` error
arm. The `Value::Str` arm's own comment explains why this is reachable: it
deliberately slices the receiver's raw bytes and returns
`Value::text_from_bytes(sliced)`, which yields a `Value::StrBytes` (not
`Value::Str`) whenever the byte range splits a UTF-8 codepoint boundary — see
`value_impl.rs:411 text_from_bytes`. Any expression that step-slices, and
whose result is then step-sliced again, can therefore hand a `StrBytes` back
into this same match with no arm to handle it.

Verified interactively (`bin/simple.exe run`) with:

```
val s = "日本語テスト"
val a = s[1:10:1]   # byte range 1..10 splits both ends mid-codepoint
print(a)             # prints replacement-char garbage — confirms `a` is
                      # Value::StrBytes, not valid UTF-8 Value::Str
val b = a[0:4:1]     # second step-slice, now on a StrBytes receiver
```

## Fix

Added a `Value::StrBytes(b) => { ... }` arm mirroring `Value::Str`: slices the
raw bytes via the same `slice_collection(...)` call, applies the same
`text_slice_audit` note, and returns `Value::text_from_bytes(sliced)` (which
re-validates to `Value::Str` if the new range happens to be valid UTF-8, or
stays `Value::StrBytes` otherwise — same reassembly contract as the `Str`
arm). Purely additive, no platform branch; applies identically on
Linux/macOS.

## Verification

Post-fix, the repro above runs clean:

```
$ bin/simple.exe run step_slice_repro.spl
9
4
```

(`a.len()` == 9 bytes, confirming `a` is the raw-byte StrBytes fragment;
`b.len()` == 4, confirming the SECOND step-slice — the one that previously
had no match arm — succeeded instead of erroring.)
