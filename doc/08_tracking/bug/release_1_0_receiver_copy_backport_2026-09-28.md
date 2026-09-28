# Release 1.0 aggregate receiver copy backport

Status: draft; focused resolver checks pass; compiler integration and native
execution remain unverified. No bootstrap or release admission is claimed.

## Scope and selected requirements

Backport the receiver-copy and math-rendering portions of main PR #1991
(`a4aa33c3492ce19e3b6a56766405fa7bc3a1a41b`) to `release/1.0`.
The working branch began at `63b50fd00c61870a8892b883255e30d5b928939f`.
The release base also includes SIMD portability PR #2005 at
`f5a3572d61530880a0b1b7c39db322deca9c759f`.

- Preserve the trait header and final field when copying a value receiver.
- Resolve outer and nested object layouts against whole-project ownership.
- Treat both resolved header decisions, true and false, as authoritative.
- Shift each nested descriptor by its enclosing object's header; recurse using
  the nested object's own header decision.
- Reject ambiguous owners whose candidates disagree about header layouts.
- Give math helpers an explicit `MathRenderable` contract and verify observable
  output for direct, trait, returned, and nested receiver paths.
- Retain release's inkwell 0.5 / LLVM18 API and dependency versions.

C collection removal is a separate backport. The owner-lifetime registry file
from #1991 is absent on release and is not introduced here.

## Release-specific prerequisites and design

Release has `AggregateCopy::type_name` for diagnostics but does not carry it
through the emitter interface. Its nested descriptors lack type and header
metadata. The release Cranelift and LLVM copy workers allocate only the
field-only byte count, while constructors reserve another eight bytes for a
trait header. This mismatch truncates a trait-bearing receiver's last field.

The backport adds `owner_has_vtable` to the outer instruction and type/header
metadata to nested descriptors, initializes unresolved decisions at MIR
lowering, and resolves them alongside native field layout qualification.
The shared emitter interface, both instruction dispatch paths, both production
copy workers, and the MIR interpreter adapter carry the new fields.

Cranelift uses its local vtable map only when native ownership has not supplied
a decision. LLVM uses the resolved decision without changing inkwell APIs.
The release behavior for invalid aggregate source values is unchanged.

The dependency-free `native_project/aggregate_layout.rs` module contains owner
resolution. Unlike the original upstream prerequisite's ambiguous-owner
fallback, it returns an error for incompatible or absent candidate layouts.
A forwarding function may copy a receiver without accessing its fields, so
the field-access resolver alone cannot guard an unsafe copy decision.

## Tests and evidence

### Executed

Three tests in the production owner-resolution module passed using a `rustc
--test` harness that imports that actual module by path:

1. Unknown and untyped owners resolve to a headerless layout.
2. Exact ownership is authoritative for both true and false header decisions.
3. Ambiguous candidates require matching headers; mixed or absent candidates
   return errors.

Local evidence: `build/receiver-evidence/aggregate-layout-tests.log`.
The harness is a generated one-line module import in the same directory;
it does not substitute a duplicate resolver implementation.

`rustfmt` parsed the changed Rust source. The repository generated-spec layout
check found zero executable `_spec.spl` files under `doc/06_spec`.

### Added, not executed end to end

- Two native-project tests cover local/imported nested header qualification and
  propagation of nested ambiguity errors through the production pass.
- The LLVM IR regression checks a two-field aggregate copy allocates 24 bytes
  (16 field bytes plus its header) and verifies the generated module.
- `test/fixtures/math_rendering_contract_native/main.spl` contains 13 absolute
  output checks. Both a plain outer object and a trait-bearing outer object
  contain a trait-bearing child, exercising both nested slot-offset cases.

### Integration blockers

Windows command, with an isolated target directory:

```text
cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler --lib --offline
```

This stopped in the pre-existing `simple-runtime` C build:
`src/runtime/startup/common/runtime_log_hosted.c:18` includes `unistd.h`, which
MSVC cannot find. It did not reach a compiler Rust result.
Evidence: `build/receiver-evidence/cargo-check.log`.

A second check used WSL's installed Rust/Cargo 1.101 nightly and a separate
`build/receiver-linux-cargo` target directory. The WSL process exited with
Windows status `0xC000013A` after manifest warnings; there was no compiler
diagnostic. An independent Linux lane observed the same external interruption
during its Git operation. This is not a Rust compilation failure or a pass.
Evidence: `build/receiver-evidence/linux-cargo-check.log`.

Windows has LLVM23; WSL inventory found LLVM13/14/17 and a local LLVM23 shared
toolchain. No LLVM18 was available. Both native-backend fixture executions
remain pending on a compatible, buildable release toolchain. Main-branch seed
results are not substituted for release compiler evidence.

Before admission, run the full Rust compiler check and the added unit tests,
then build and execute the 13-check fixture under LLVM18 and Cranelift with
stub fallback disabled. Repository compiler/lib/MCP checks and runtime/MCP
smoke gates remain required for release readiness.

## Review

An independent reviewer approved the static backport structure after checking
MIR construction, both dispatch paths, header allocation, nested offsets,
authoritative false decisions, ambiguity errors, and LLVM18 API preservation.
This review does not establish runtime or release admission.
