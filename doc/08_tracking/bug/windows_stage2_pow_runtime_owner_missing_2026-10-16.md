# Windows Stage 2 link misses the integer power runtime owner

Status: OPEN; runtime composition investigation. No repaired compiler or
application execution is admitted. This is a new native Windows reproduction
of the provider-availability gap recorded in
[the earlier power workaround](llvm_power_declaration_workaround_2026-10-14.md).

## Actual failing boundary

The immutable compiler snapshot `f612b3f68d6fc315b44df0cff8ec8a6f1db0f5da`
under `D:/dev/simple-smux-bootstrap-20261016` completed its Rust seed and
native-all construction, then compiled 1349 Stage 2 modules. Canonical campaign
session 79327 terminated with exit 1 at the native link, before a final Stage 2
executable, Hello compile/run, admission, or any smux build.

Retained log:
`build/bootstrap/smux-campaign/logs/x86_64-pc-windows-msvc/stage2-native-build.log`
in that frozen checkout. Its terminal diagnostic is:

```text
lld-link: error: undefined symbol: __simple_pow
>>> referenced by libspl_objects.a(mod_493.o):(compiler__mir__mir_instruction_graph__mir_fold_binop)
clang-cl: error: linker command failed with exit code 1
```

The canonical final verdict is ABORTED at stage2, exit 1. This is not the
7200-second watchdog boundary. Parent 756, Bash 8680 and builder 23692 were
absent after termination. The private object staging and caches remain intact;
they must not be deleted or labelled admitted because compilation progressed.

## Confirmed ownership and next repair

The caller declares an explicit `i64, i64 -> i64` integer-power ABI. The
existing implementation lives in `runtime_core_intrinsics_impl.h`, reached
through the monolithic runtime or its standalone `runtime_core_intrinsics.c`
owner. The current pure-Simple core-C source manifest already names that owner.
This source evidence does not yet identify which actual selected archive or
link-input boundary lost it; inspect retained object symbols, archive members
and the exact linker arguments before selecting a repair.

Do not replace the caller's power expression, add another exponentiation
algorithm, duplicate LLVM declarations, or relaunch the unchanged full build.
Preserve the 1349 compiled modules and bind any supported relink/new attempt to
its actual changed runtime composition, producer and source hashes. A diagnostic
relink is not canonical admission. The exact resulting compiler must compile
and execute Hello before either dependent smux phase can start.

Required regressions include integer power's existing zero/negative exponent
behavior and the production `mir_fold_binop` native fixture. A linked compiler
alone cannot establish these semantics. General SSpec and docgen remain
unavailable until a suitable admitted runtime exists.

Bug database registration is pending its canonical writer: the local
`bug_db.sdn` has a checksummed database header and no admitted writer is
available. This standalone report preserves the actionable failure without
forging a database checksum or WAL transaction.

## Scoped source composition repair

The failure is a missing provider member, not a missing IR declaration.
`build_c_runtime_library` in
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` omitted
`runtime_core_intrinsics.c` from its `runtime_inputs`. The Stage 2 native link's
`core_c_bootstrap_supplement` is built by this exact owner. The Pure-Simple
backend's `runtime_core_c_sources_v1` already includes that translation unit.
Frozen f612 and the editing checkout had byte-identical runtime source,
implementation header, Pure-Simple runtime list and MIR caller at diagnosis.

The authorized bootstrap-only manifest repair adds the existing translation
unit and its private implementation header to the source/fingerprint inputs.
It changes no Rust or Simple power algorithm, C implementation, runtime ABI,
LLVM declaration, target variant, or application expression. Fingerprint and
exact-member checks naturally reject the former incomplete archive on the
next supported rebuild; immutable retained archives are not overwritten.

The existing real core-runtime archive ABI test now requires the normalized
`__simple_pow` definition and counts exactly one defining owner in its actual
symbol listing. This is a bootstrap archive-composition regression, not a Rust
seed substitute for product or Simple SSpec execution. It remains unexecuted
pending the canonical build owner's finite qualification plan.

The retained production fixture
`test/fixtures/compiler/mir_integer_pow_abi_native.spl` exercises the actual
`mir_fold_binop`: 12 finite integer cases including exponent zero and negative
exponents, six floating cases, and two invalid-operation controls. It does not
copy the implementation. It likewise remains UNRUN; source inclusion alone is
not proof of those semantics, signed-overflow behavior, or 32-bit Pow ABI.

The existing archive regression's symbol-set helper normalizes all leading
underscores and uses `-g --defined-only`; the added presence check therefore
uses `simple_pow`. Its exact-owner count reuses the test's existing separate
`nm -g --defined-only` output, so undefined references cannot inflate the
definition count. On Windows that existing test requires a COFF-capable `nm`
on PATH. No tool-policy change or cargo test execution is implied by source
review or whitespace validation.

The build owner may separately compile this one existing C translation unit
with the retained matching Win64 toolchain/flags and relink the preserved 1349
module objects using a fully recorded, source-derived reconstructed linker
command: the original nonverbose campaign did not retain its actual linker
argv. That is a diagnostic new
composition and must be labeled unadmitted. It must check all intrinsic-owner
overlaps, retain new hashes/logs, and require actual Hello compile/run before
any dependent product phase. The diagnostic relink does not repair the frozen
source manifest or admit a canonical compiler by itself.

The one-unit collision audit found that both Rust runtime archives also define
`__simple_intrinsic_bounds_check`. The existing linker recipe already uses
`/FORCE:MULTIPLE`; no additional duplicate/unresolved-symbol relaxation may be
introduced for this repair. Source inspection finds the same signed-i64 ABI,
out-of-range exit and valid-index zero return in both implementations. Actual
map/extraction evidence must still identify the retained owner; a successful
link alone cannot close this ownership gate. The minimal manifest change is
therefore conditional on resolving that gate, not a canonical qualification.
