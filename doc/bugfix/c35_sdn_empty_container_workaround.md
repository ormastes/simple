# C35 SDN empty container source workaround

Compiler issue: [#2982](https://github.com/ormastes/simple/issues/2982), still open.
The C35 runner attempted all 251 MIR modules and reported payload type mismatch
at slot zero for `lib.common.sdn.value.SdnValue.Dict` and `.Array`. These fatal
messages contain no source span; an exact diagnostic-to-function association
has not been proven.

The retained `value.spl` HIR cache identifies the relevant empty constructors:
`empty_dict` at cache line 13303 contains an empty DictLit at source line 60;
`empty_array` at cache line 20329 contains an empty ArrayLit at source line 57,
with a synthesized Int32 element annotation. Both are source-supported
workaround candidates, not a claim that their association with the two fatal
messages has been established at runtime.

Evidence root:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c35-producer-c35-runner/`.
Use `normalized-mir-errors.json` and retained HIR cache
`b0652baefd31e9e9f81173a4c920b6a187b3c57b995b8f184c0b1c3fd6ed903f.hir`.
Frozen source: `ea9224a83a64cd20e21d013cf1c2652f891999c4`;
producer SHA-256: `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`.

The user requested behavior-preserving source workarounds before separate
compiler repairs. Both methods now construct the same fresh empty container
in an explicitly typed local before wrapping it in the same enum variant.
No contents, evaluation effects, return types or validators change. There is
no cached/shared singleton and no fallback payload. The compiler's existing
contextual literal typing remains unchanged; why its native path rejected
these payloads remains a separate investigation under #2982.

The authored native fixture checks array/dict identity, zero length, rendering
and nested rendering. The SSpec checks the same public API contracts. Both are
unexecuted pending coordinated resources. Native acceptance requires actual
ARM execution with exit zero and `sdn_empty_container_workaround: PASS`, then
explicit LLVM 18 RISC-V object/ELF machine 243 qualification. The unchanged
runner must subsequently show whether these two diagnostics disappear.
No existing failed C35 command was rerun and no compiler was built here.

This workaround does not claim to fix SDN mutation/return-copy limitations,
the separate enum literal-pattern failure [#2981](https://github.com/ormastes/simple/issues/2981),
or callback failures. Keep #2982 open until a separately reviewed underlying
compiler repair has native proof.
