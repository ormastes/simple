# BUG: native path — `.push()` on untyped arrays fatal + `[""; N]` fill-literal emits invalid IR

**Status:** OPEN (found 2026-07-11 during #138 Phase-2 --entry injection attempt)

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

## Context

All three blocked the pure-Simple `--entry` injection in bootstrap_main.spl
(#138 Phase 2, reverted). Fix direction: add rt_array_push interception for
Unresolved receivers; type rt_array_repeat results as tagged i64 in
translate_copy_move; root-cause the concat drop in extract_rt_string_array.
