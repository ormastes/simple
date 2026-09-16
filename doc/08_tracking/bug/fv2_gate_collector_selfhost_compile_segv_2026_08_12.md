# FV2 gate collector self-hosted compile SIGSEGV

## Status

Open compiler/runtime blocker. FV2 collectors are not verified until their
focused specs execute successfully.

## Composite admission evidence

The clean composite build linked all 835 units, but its mandatory Stage 2
sanity gate quarantined candidate
`f6e48bc8e878b1ad4b9abc9a29280fa80ba920f3059494ef7f4c7ea7c4e31df9`.
The exact retained evidence is under
`/mnt/data/.simple/bootstrap/composite-forensic-admission2-20260812/output/stage3/x86_64-unknown-linux-gnu/rejected-stage2/f6e48bc8e878b1ad4b9abc9a29280fa80ba920f3059494ef7f4c7ea7c4e31df9/`.
Both `--version` and unsupported-command probes exited 132 with
`runtime error: invalid field receiver`. This independently reproduces the
receiver failure after a clean full link; it is not an FV2 test failure and the
quarantined binary is not admissible.

## Reproduction

The admitted pure-Simple LLVM compiler at
`/mnt/data/.simple/bootstrap/authority-22d7-llvm/output/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
passes `--version`, but compiling each owner below terminates with status 139:

- `src/compiler/90.tools/verify/formal_gate_collectors.spl`
- `src/compiler/90.tools/verify/formal_os_hardware_gate_collectors.spl`
- `src/compiler/90.tools/verify/formal_product_gate_collectors.spl`

Command shape:

```text
<admitted-simple> compile <owner>.spl --format=smf --output=/tmp/<probe>.smf
```

The source was first split into core Gates 0–3, OS/hardware Gates 4–5, and
product/release Gates 6–7. All three reproduce, pointing to a shared
compiler/import/aggregate path rather than file size alone.

A noninteractive GDB run against the smallest product/release owner initially
localized one fault to parameter lowering:

```text
SIGSEGV
HirLowering.lower_param
HirLowering.lower_function
HirLowering.lower_module
CompilerDriver.lower_and_check_impl
CompilerDriver.compile
run_compile_bootstrap
```

The absent-default branch in `HirLowering.lower_param` used a value-producing
conditional expression. Current source now initializes the nil/default HIR
expression explicitly and only reads `p.default` under `p.has_default`, so an
admitted compiler cannot eagerly materialize the absent parser payload.

A second GDB run while compiling `verification_ir.spl` reached a distinct
fault after three clean dependency sources:

```text
SIGSEGV
HirLowering.field_module_callable
HirLowering.lower_hir_expr
HirLowering.lower_hir_stmt
HirLowering.lower_impl
HirLowering.lower_module
CompilerDriver.lower_and_check_impl
```

That resolver scanned `SymbolTable.symbols` and read each `HirSymbol`
aggregate to rediscover `(defining_module, name)`. `SymbolTable` already owns
the scalar `qualified_functions` index, but imported-function lowering never
populated it. Current source now binds that index before bootstrap-only symbol
renaming and performs module-call lookup solely through
`lookup_qualified_function_raw`. This removes the aggregate scan and preserves
the semantic module/member key independently of local aliases.

Both repairs require a newly admitted current-source compiler before they can
serve as runtime evidence; static source assertions alone are not acceptance.

## Related evidence

The newer bootstrap at `/mnt/data/bs2/perf-integrated-50a996` produced no
admitted compiler: its Stage-2 log reports 44 pre-existing field-type inference
failures, then the guard terminated it with exit 143. The older Cranelift
admitted binary traps with `invalid field receiver` and exit 132 on an
unrelated fixture.

## Current-parser diagnostic evidence

The deployed `bin/simple` is still a Rust bootstrap seed built before the
continued-inline-condition parser repair. It rejected
`verification_ir.spl` with `expected Fn, found Var`. Current parser source owns
an exact regression,
`continued_inline_guard_keeps_following_impl_local`, which executed with one
passing test. A freshly rebuilt bootstrap driver then parsed the same FV2 owner
successfully and advanced to the expected standalone-SMF capability rejection
(interpreter-only pattern matching), proving that the earlier parse diagnostic
was stale-tool evidence rather than malformed FV2 source.

The focused `lean_backend_spec.spl` run with that current-parser diagnostic
driver admitted the source graph and reached execution, but exceeded both the
default 60-second monitor and one bounded 180-second retry. No assertion result
was produced and no PASS is claimed. Per the three-cycle guard, this exact
acceptance check is not retried again in the same session. This Rust-driver
evidence is diagnostic only; closure still requires the pure-Simple runtime in
the Required closure below.

## Struct receiver root cause and integrated runtime owner

GDB and archive disassembly localized the quarantined candidate's exit-132
failure to `rt_struct_receiver_valid`: native aggregates pass the canonical
heap-tagged pointer (`raw | 1`), but the linked runtime object hashed that
encoded value while `rt_struct_alloc` registered the raw address. The rejected
runtime objects were built at `2026-08-12T14:20:33Z`; the clean authority
worktree committed the tagged-receiver repair later at
`2026-08-12T14:46:59Z`. The rejected artifact therefore genuinely predates the
repair; no stale Cargo/cache provenance claim is supported.

The clean main runtime owner now matches the two committed authority changes:
it owns the paired struct allocation registry, decodes only raw tag `000` or
canonical heap tag `001`, rejects all other low-bit patterns before lookup,
checks bounds without overflow, unregisters before free, and serializes
validation/free registry access. The adjacent C selfcheck compiled directly
against this owner and passed 1,033 assertions including 1,024 concurrent
post-free rejections. The authority worktree's newer tagged/malformed-tag test
is retained in its own committed lane; its other dirty companion files were
not copied or overwritten here.

The stronger authority selfcheck was also compiled against the integrated main
runtime owner. It passed canonical tagged lookup, malformed-tag rejection,
raw-allocation non-authority, bounds, post-free rejection, and 1,024 concurrent
post-free probes. Disassembly of the exact Stage-2 runtime archive confirms the
binary performs the malformed-tag test and `and $~7` decode before hashing the
registry key. The Stage-2 receiver gate's missing-compiler, accepted-output,
wrong-output, and mandatory pre-admission wiring cases all pass. These close
the runtime primitive itself, but not the compiler admission that consumes it.

## Clean Stage-2 admission result

The clean authority build at commit `5a42094a92e96d7ce4069880af2eb38d577e2bcc`
completed Stage 2 with candidate SHA-256
`a4bc8f44b74094b07d4c4dfbcb586ed291cbc89655464b6fba0a0c6f2b847e55`.
Its generic sanity receipt reports stable before/after hashes, the exact
`simple-bootstrap 1.0.0-beta` identity, rejected unsupported command, and both
frontend-smoke modes passing. The exact-runtime mutable receiver probe also
built and executed successfully.

That evidence is narrower than FV2 compiler admission. The first real
`compile --format=smf` owner probe still exited 132. GDB localized it to
`CompileContext.has_errors`; its receiver was `0x16861d1`, whose decoded memory
contains source text rather than the 144-byte `CompileContext`. The runtime
guard therefore correctly rejected a corrupted receiver. A native-build of the
focused collector then failed discovery at the continued multiline inline
guard in `formal_delivery_gates.spl`. Three bounded compile cycles were used;
no FV2 owner PASS is claimed. The receiver admission gate is now wired before
the admitted-copy step, binds typed evidence, checks runtime immutability, and
quarantines failure, but a broader real-driver receiver fixture remains
required.

The source-side repair removes the corrupting transport rather than weakening
the runtime guard. Source loading, ordinary and streaming parsing, ordinary and
streaming HIR lowering, and bootstrap MIR lowering now mutate the one
driver-owned `CompileContext` and return only booleans. Orchestration consumes
those booleans without destructuring or reassigning copied contexts. The
bootstrap native fallback also writes its MIR result into the same context
handle. A 20-case contract regression rejects local context copies, tuple
returns, tuple-destructuring callers, and parser-scope promotion in either
driver constructor. Runtime acceptance still requires rebuilding and admitting
a compiler containing the complete repair.

Highest-capability review rejected the concurrent
`rt_transient_heap_promote(ctx)` alternative. That primitive requires an active,
paused transient parser scope; compiler-driver construction occurs outside
such a scope, so asserting promotion would break normal creation and would not
repair the receiver ABI. The existing entry-closure test now expects the
authoritative phase-1 context rather than the removed `loaded_ctx` copy.

The ownership rule therefore covers the active phase 1–4 pipeline boundaries.
The stale pipeline source-contract tests were updated to the authoritative
owner. This closes the known aggregate-copy transport pattern in those paths;
it does not by itself prove the native ABI or admit the rebuilt compiler.

The isolated phase 1–3 lineage built 835 units and linked candidate SHA-256
`7b8b1ab66b8ec39266b59659670053ab5171ebdb9911fdd7490dc086843f645c`.
Mandatory sanity rejected and quarantined it: both identity probes exited 132
with `invalid field receiver`, while only the bootstrap-mode frontend smoke
passed. That is expected negative evidence that phases 1–3 alone do not close
the aggregate transport defect. Isolated commit
`edaf1d6e28b363ea12e2da8f1eae1b970b3a81d2` adds the phase-4 bootstrap MIR and
native-fallback repair; its second bounded build writes a separate candidate
and must independently pass every admission gate.

Cycle 2 linked SHA-256
`e87c7a6ba89d01593e4f8ceb033f1c4eb4a9801dcdf7386936099e290eb353cb`,
but the first `--version` discriminator still exited 132. GDB moved the exact
fault out of the driver pipeline and into a pre-main dynamic initializer:
`R_RISCV_CALL_PLT` called `rv64_encode_contract`, which constructed and passed
`TargetPreset`, numeric-capability, and RISC-V target-contract aggregates just
to obtain the fixed ELF relocation tag 19. RV32 and the canonical ELF writer
already own that value as a scalar constant. RV64 now does the same, while the
runtime contract function remains available for actual target queries. A
two-case source guard rejects reintroducing the aggregate initializer. The
third and final bounded rebuild uses isolated commit
`daac003c288d0396110d3f65333866edaf4e169d`; another failure ends this repair
cycle with the remaining call site recorded rather than triggering a fourth
build.

The third build compiled four changed units, reused 831 exact cache entries,
and linked candidate SHA-256
`659769875ed3239ba8a6b1e369f8db3b699e12a248f1fe42612eebaddf00d2d9`.
Its first `--version` discriminator still exited 132. GDB identified the next
pre-main instance of the same class in `isel_riscv32`: module global
`RV32_WORD_SIZE` calls `rv32_linux_contract().pointer_bits / 8`, transporting a
`RiscvTargetContract` aggregate merely to obtain scalar 4. The required next
step is a bounded inventory of all dynamic scalar globals that call
aggregate-returning functions, followed by one reviewed class-wide repair and
one new build. The mandatory three-cycle cap is reached here; no fourth build
or compiler-admission claim is permitted in this repair turn.

The bounded class inventory found two remaining executable native-backend
globals of the direct `aggregate_factory().field` form: RV32 and RV64 word
sizes. They are now compile-time ISA/ABI constants 4 and 8. The corresponding
runtime target-contract functions remain unchanged for real target queries.
The regression now checks the RV64 relocation tag, both word sizes, and scans
the full native backend for any direct module-scalar aggregate-field
initializer; all five cases pass. Fenced documentation examples were excluded
from the executable inventory. Per the cycle cap, this source closure is not
yet runtime admission evidence and no fourth bootstrap was launched.

The next reviewed cycle produced candidate
`963a1fe2da9631ac2e8f08cccfcc151c1a7170d71876a35245fb640a17fcf30a`,
which passes the exact bootstrap identity. The receiver gate then exposed two
separate truth defects. First, it validated a runtime archive and incorrectly
passed that file as `--runtime-path`, although native-build requires the
containing provider directory; the resulting probe left `rt_set_args`
unresolved and called address zero. The gate now validates the exact archive
but passes the provider directory, and its five contract cases pass. Second,
the real provider-linked probe showed guarded Struct allocation still using
raw `rt_alloc`. The reviewed paired-owner source repair uses
`rt_struct_alloc` for Struct and Tuple aggregates and strengthens the smoke to
cover class, tuple, text, and value-copy behavior.

A cache-backed rebuild then compiled only four units and reused 831, but its
probe disassembly still called `rt_alloc`; the backend object was stale despite
the changed semantic owner. That candidate is rejected as stale evidence. The
third and final cycle for this turn uses a new empty cache. It must compile the
full closure before any receiver or FV2 admission claim.

Clean cycle 6 compiled all 835 units with zero cache reuse and linked candidate
SHA-256 `fb5ef13eac5149ae72b50c83534916758f10d14b9952374bd68f5258dfad51bb`.
It passes exact identity and unsupported-command behavior, but its real
provider-linked aggregate smoke still rejects. Disassembly is unambiguous: the
class allocation calls `rt_alloc`, then the correctly wired receiver guard
rejects it. Because the clean pure-Simple source owns `rt_struct_alloc`, this
is not another source-cache miss. The Cranelift emission is delegated through
the frozen runtime compiler provider, whose Rust emitter predates the paired
repair in reviewed commit `bd605cb24f5`. This supplies the required evidence
that the pure owner delegates correctly and the remaining defect is below that
boundary. The three-cycle cap is reached. The next lineage must rebuild and
freeze an exact runtime provider containing the matching emitter repair before
another compiler candidate can be admitted.

The isolated continuation lineage now records that missing boundary repair in
commit `18edc1fe9f8a4c4313956b3a8a82824990d7b04c`: both Rust Cranelift aggregate
emission and the LLVM object/copy paths allocate field-bearing aggregates via
`rt_struct_alloc`. The bounded rebuild command is:

```sh
cd /mnt/data/.simple/bootstrap/fv2-context-authority-20260812/worktree
timeout -k 30s 2700s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift \
  --output=/mnt/data/.simple/bootstrap/fv2-context-authority-20260812/cycle7 \
  --fresh-cache --jobs=1 --no-mcp
```

Its exit alone is insufficient. Admission must bind the newly frozen provider
hash, pass the real provider-linked receiver smoke, and then pass the exact
candidate identity and minimized FV2 probes.

Cycle 7 did supply that provider: its Stage 2 candidate
`d656135ab7aff602f54a5985d9ca4a5029945943b2c8e5afabcb6b1128212461` passes
both sanity and the real guarded aggregate receiver smoke. Stage 3 then exposed
a distinct call-ABI defect. The generated `CompilerDriver.load_sources_impl`
correctly loaded `self.ctx`, but `CompileContext.has_errors` had been lowered
with a zero-parameter callee signature; MethodCallStatic consequently dropped
its receiver. GDB confirms the failure at `CompileContext.has_errors`, with the
driver object still in the argument register. A historical commit changed the
affected instance queries to `me`; that is explicitly rejected as a fix because
it changes immutable method semantics and masks the general ABI defect.

The canonical source repair is parser-owned: plain `fn` in an aggregate body is
an immutable instance method even with zero explicit source arguments, so the
Rust parser emits an ABI-visible `self`; only explicit `static fn` is
receiver-less. Import discovery carries both arity and receiver-kind metadata,
and native codegen rejects missing or contradictory receiver signatures before
argument adaptation. Pure-Simple HIR/MIR retains the owner-context receiver and
fails closed if the ABI receiver is absent. Cycle 8 is the single clean rebuild
for this root cause; it must still pass Stage 3 and all admission probes before
any promotion.

Cycle 8 completed the corresponding clean Stage 2 rebuild and passed its Stage
2 sanity gate, but the Stage 3 self-host invocation again terminated with
signal 11 (exit 139) and produced no Stage 3 binary.  The empty redirected
Stage-3 log means the crash occurs before the in-process compiler can emit a
diagnostic; this is distinct from a Lean or FV2 proof failure.  The
parser-owned receiver repair is present in source and its focused
parser/compiler checks pass, but no self-hosted native receipt was obtained
here. Bootstrap admission therefore remains HOLD: do not promote the
candidate or treat the Rust seed as runtime evidence. Direct observation of
the same command may continue running long enough to hit the bounded timeout,
so this failure is treated as timing/cache-sensitive evidence, never as a
passing self-host result.

## Required closure

1. Repair the `CompileContext` construction/call ABI so a real SMF compile
   reaches `has_errors` with the exact registered context allocation; retain a
   regression that distinguishes it from source-text buffers.
2. Admit a current-source pure-Simple compiler containing that repair plus the
   parameter and qualified-call resolver repairs; do not use the Rust seed for
   acceptance.
3. Re-run both minimized compile probes and require normal exit without host
   signals.
4. Execute all focused Gate 0–7 specs once, followed by required compiler/lib
   and MCP/LSP verification.
