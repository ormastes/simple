# C35 Result optional payload source workaround

Compiler bug [#2981](https://github.com/ormastes/simple/issues/2981) remains open.
The frozen C35 runner failed MIR with an unsupported literal kind inside an
enum payload. Its diagnostic had no source location. A bounded structural
audit of its 251 retained HIR caches found an `Ok` enum payload with a
`HirPatternKind.Literal(HirExprKind.NilLit)` at
`src/app/io/rt_hal_isolated_host.spl:157:16`, the source arm `Ok(nil): ()`.
The expression span is 7019..7022; its enclosing pattern span is empty, which
explains the missing diagnostic location. The MIR literal helper supports only
integer, boolean and text literals, so this HIR node takes its failure branch.

Retained cache: `0d31d726204855bad98bdd8773fc32ff7faf307a76f623b51e6d1885b04bbbe6.hir`,
enum pattern begins at line 14474. Frozen source:
`ea9224a83a64cd20e21d013cf1c2652f891999c4`; producer SHA-256:
`96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`.
Evidence root: C06 `build/native_probe/phase3-whole-20261011-c06/c35-producer-c35-runner/`.
The audit script and result are retained in the owned workaround worktree's
`build/native_probe/c35-literal-audit/`; it decodes supported pattern/type forms,
not the entire HIR module schema, and is not a completeness proof.

The adjacent `Ok(Some(chunk))` and `Ok(nil)` arms are replaced by one
`Ok(maybe_chunk)` arm followed by `if val chunk = maybe_chunk`. The process read
still occurs once per iteration. Present chunks use the same capacity check
and append in the same order. Absent chunks do nothing. Errors, EOF parsing,
sleep, timeout and task state are unchanged. No error is suppressed and no
compiler validator is relaxed.

The native fixture exercises the same Result/optional binding with present
data, present empty data, absent data, exact capacity, overflow, EOF and other
errors. The SSpec checks payload/error distinctions. These are grammar and
branch regressions, not execution of the private host process loop. Both are
authored but unexecuted. ARM execution and a genuine explicit-target LLVM 18
RISC-V object remain pending, followed by the runner object gate. No compiler
construction or unchanged C35 retry was performed for this patch.

The previously suspected `Ok((root, issues))` arm in `plan_sdn.spl` already
appears as an enum payload Binding and generated tuple-index bindings in
retained HIR; it is unchanged. A separate compiler repair must support nested
nil payload patterns and obtain native evidence before closing #2981.


## Native counterexample and typed text boundary (2026-10-11)

The source workaround at `3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a`
compiled with C35 producer
`96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`
and the host-gpu runtime capsule, but ARM execution returned **1**, stdout empty.
Artifact SHA-256:
`6be04f79893d353fb1d838246df57966f3c3a715bd10970b5c1cbacc11e697a4`.
This is a failed runtime assertion, not a successful workaround qualification.
First assertion: `consume(Ok(Some("bc")), "a", 3) == "abc"`.
Retained evidence is under
`/home/yoon/dev/simple-runner-enum-workarounds-20261011/build/native_probe/c35-workaround-qualification/result_optional_payload_workaround/arm-attempt2/`.
The source/producer/runtime before/after guards were equal; ELF machine is 183.

Bound disassembly of consume at `0x129c24` shows Result payload extraction at
`0x129c58`, presence check at `0x129c60`, and optional unwrap at `0x129c6c`.
The present branch calls string length normally, then at `0x129d70` calls
`rt_raw_i64_to_string` on the unwrapped text handle before concatenation at
`0x129d7c`. Thus the unwrapped binding lost text provenance: concatenation
formats its handle as an integer. This evidence does not establish that C36
has the same defect; the failed fixture used the exact C35 producer above.

A second source workaround carries the already-unwrapped value through a
`text -> text` identity helper before length and concatenation. This preserves
Result/Option distinctions and the original process-read count, capacity check,
append order, EOF/error handling and timeout. It does not parse or format the
payload, suppress an error, or weaken a compiler validator. The standalone
native fixture and SSpec use the same boundary and retain all prior assertions.
A changed-source native replay is required; until then this remains unqualified.
The passing SDN container fixture is a separate result and must not be rerun or
credited to this optional-result repair. Original source/artifact receipts stay
at their frozen paths. The underlying pattern/text-provenance bugs remain open.
