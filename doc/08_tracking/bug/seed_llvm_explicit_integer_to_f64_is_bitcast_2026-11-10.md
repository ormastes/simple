# Seed LLVM explicit integer-to-f64 casts preserve integer bits instead of converting

Status: **component verified; constructor and descendant verification pending**.
The numeric diagnostic campaign's original six attempts remain recorded.

Canonical bug ID: `seed_llvm_explicit_integer_to_f64_is_bitcast_2026-11-10`.
Severity: **P1**. Canonical shard status is
`fix-implemented-verification-pending`, never closed on component COFF alone.
The later root-interpreted user continuation permits one actual native
harness-control operation and two bounded Rust component rows while retaining
the original six diagnostics. Helper02 controls have since passed; they are
harness evidence. Both exact baseline component tests subsequently failed their
intended width-correct conversion assertions. The first GREEN build failed
before tests because the pinned Inkwell custom-width API requires NonZeroU32
and returns Result. An explicit bounded corrective row used the fixed-width
constructors; both exact x86/x64 component tests then passed. All earlier
attempts and failed-build evidence remain preserved.

## Retained live defect evidence

`build/review/linux-capacity/numeric-constant-diagnosis/BUG.md` in the isolated
`simple-windows-linux-capacity-unavailable-20261109` worktree records the real
c56 positive native probe: digit/character control passed, then
`FAIL:to-float-equality`, exit **14**, complete/quiescent, peak 20,744 KiB.
Its generated object begins with constant bytes
`18000000000000006000000000000000` rather than the independently expected
binary64 bytes `00000000000039400000000000005940` for 25.0/100.0. This is a
compiler defect, not evidence that runtime text-to-float conversion is broken.

The same retained worktree contains
`build/review/linux-capacity/numeric-lldb-observation4/observations.sdn`
(SHA-256 `31c2726819b861ea4144efa418e1a7d62c6444a95dc07402d8699cfda396e75a`)
and `captured-module.ll`
(`308894a0ef4a623067b38b167cab655de7b38e1a72f1541928c88a7b2b23e8d9`).
They capture already-corrupt MIR Float payloads before serialization;
FloatLexeme helper calls were zero. Historical diagnostic notes correctly
left the owner unresolved at their time; the numeric-cast source/machine
trace below supplies the later root cause without modifying those receipts.

## Actual producer and first proven upstream defect

The failing pure-Simple producer is
`build/review/phase2-d128-producer-20261107/construction3/output/simple-bootstrap.exe`,
SHA-256 `c56bbec927b380e9d50820c7c81ebbaf6de5648c34bf879c895f27fb27df1518`.
Its receipt binds source commit
`4fa7f05fa5ff55af6ac3199fea563e3800ed8b74` and constructor binary SHA-256
`86f93d6c179c075fbe6a27cc5f4c888d187d547783d119ef0c4cd8b3539bd053`.
The constructor hash is not a Git revision. Its retained physical source is
`build/review/seed-checked-getter-constructor-04b8/source`.

The pure-Simple frontend's `parser_types_utils.spl:59` computes
`result * 10.0 + (code - 48) as f64`. Targeted disassembly of the actual c56
image shows:

```text
1406bc209  addq   $-0x30, %rax
1406bc213  vmulsd %xmm7, %xmm6, %xmm0
1406bc217  vmovq  %rax, %xmm1
1406bc21c  vaddsd %xmm1, %xmm0, %xmm6
```

The decimal digit integer is bit-reinterpreted as a double; there is no
numeric `cvtsi2sd` conversion. Accumulating the denormal digit bit patterns
explains raw words 25 and 100 before later tagged-float decoding masks low
bits to 24 and 96. The final debugger observation independently found already
corrupt `MirConstValue.Float` payloads `0x18`, `0x0`, `0x60` at backend entry
for source literals 25.0, 0.0 and 100.0. The exact intermediate payload values
were not dynamically captured; the static instruction sequence is the proof
of the earlier numeric-cast defect, not a claim of a newly observed boundary.

Rust MIR `lower_cast_expr` emits a real `MirInst::Cast` with semantic source
and target types. However, LLVM `functions/casts.rs::compile_cast` handles
Any/text-to-integer decode and then returns `source_val` unchanged for all
other casts. Later ABI coercion correctly bitcasts an i64 word into f64;
that representation operation cannot substitute for the missing numeric
conversion. Release `93d184f65dd090200ae5cbf7808b2b5892a457bb` retains the same
no-op `compile_cast` implementation.

## Candidate scope

Explicit primitive signed/unsigned integer-to-f64 casts now emit `sitofp` or
`uitofp`, restoring the source integer's semantic width before conversion.
The decision uses semantic `from_type` and `to_type`, not merely LLVM
`IntValue`, so Any, text, nominal words and existing float bits retain their
previous paths. Generic ABI bitcasts and Any/text-to-integer decoding remain
unchanged. F32 targets and other cast categories are outside this candidate.

The repair is in the bootstrap seed owner that generated the broken parser;
it does not patch the serializer or convert every frontend float to a lexeme.
The frontend deliberately defaults to `ExprKind.FloatLit(f64)` and selects
`FloatLexeme` for module constants and match patterns. Changing that default
would route around the miscompiled parser while leaving numeric casts wrong.

## Authored regressions and required verification

The focused Rust tests call the actual LLVM `compile_cast` owner for all
eight primitive signed/unsigned integer widths. X86 and x64 modules require
`sitofp`/`uitofp`, verify with LLVM, emit COFF objects, and validate their
machine headers. A separate ABI-only function retains bitcast behavior.
The actual x64 baseline failed on an i8 cast retaining an i64 bitcast; the x86
baseline already emitted sitofp i32 but omitted semantic i8 width restoration.
Both tests therefore detect width-correct numeric conversion, rather than
merely accepting a nonempty artifact. Semantic-gate checks exclude Any, text,
bool and float words.

`test/fixtures/compiler/seed_numeric_integer_f64_cast/main.spl` retains the
digit parser shape, explicit signed/unsigned casts and an enum Float payload.
The two Rust component tests **PASS** on the actual corrected source SHA256
`3ae6b7cd24f5c1c96bd07daaf0e873e7062e1e4ab5dfdfe51b5aabd859c26f92`.
Each test verifies LLVM IR, emits COFF into memory and checks its target header;
individual emitted object bytes are not retained as standalone artifacts.
The actual test executable is retained outside Cargo's target directory with
SHA256 `0fb45c09e9002b3bf006173c83daedfb16dc028d4234c6813be946e3b78dc95b`.

Evidence owner: `simple-seed-llvm-numeric-f64-control4-20261110`, frozen base
`aedc3c43d6f1f562a1bfb3cb7370b6ae0072850f`. `red/` retains both expected
failures; `green/` retains the compilation failure; `green02/` retains both
passing exact-test logs and the executable. `green02.identity.sdn` binds the
actual outputs; `green02.rss.env` records terminal exit0, enforcement and
quiescence, peak job commit4389540 KiB under the8000000 KiB ceiling.

The Simple native fixture remains **NOT_RUN**. Rebuilding the constructor,
producing a descendant compiler, executing numeric/Hello witnesses and
qualifying the full CLI/test runner remain separate work. This component PASS
does not close the canonical P1 bug or qualify those descendants.
