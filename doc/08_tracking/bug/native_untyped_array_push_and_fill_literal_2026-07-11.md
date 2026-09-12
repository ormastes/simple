# BUG: native path — `.push()` on untyped arrays fatal + `[""; N]` fill-literal emits invalid IR

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-15 -> CLOSED-STALE 2026-09-12):** source implemented for all three facets. Historical
native evidence covers push/fill; strict concat-forwarding execution remains
pending.

## Symptom 1: .push() unresolved

`.push()` on an untyped array receiver is a fatal `unresolved method call` —
the untyped-receiver runtime fallbacks cover string methods
(len/starts_with/ends_with/substring) but no array mutators exist
(`rt_array_push` interception analog).

## Symptom 2: fill-literal invalid IR

`[""; N]` fill-literals emit invalid LLVM IR: the `rt_array_repeat` result is
mis-typed `ptr` by `translate_copy_move`
(`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:619`).

## Symptom 3: string-concat result dropped crossing rt_native_build

A string-concat result passed through `extract_rt_string_array` into
`rt_native_build` vanished (injected token lost; the build silently flipped to
a full 10862-file compile — the wrong-entry default in
`rt_native_build_silent_wrong_entry_default_2026-07-11.md` compounding).

**Resolved in source:** text `+` lowers to `rt_strcat_tagged`, whose C owner
returns a registered tagged `RtCoreString`; the pure-Simple runtime mirrors the
same ABI via `rt_string_concat`. The real Rust `extract_rt_string_array`
consumer is covered by
`scripts/check/check-native-concat-string-array-forward.shs`, using
`rt_execute_native` to distinguish a preserved concat argument from a dropped
one under default LLVM and explicit Cranelift. Execution requires the bootstrap
`SIMPLE_RUNTIME_PATH/libsimple_native_all.a` provider and remains pending.

## Context

All three blocked the pure-Simple `--entry` injection in bootstrap_main.spl
(#138 Phase 2, reverted). Fix direction: add rt_array_push interception for
Unresolved receivers; type rt_array_repeat results as tagged i64 in
translate_copy_move; root-cause the concat drop in extract_rt_string_array.

## Triage 2026-09-12
The 2026-07-15 status already noted concat-forwarding execution remains pending; still unexecuted 2 months later. Older than 45 days with no cheap repro re-run; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
