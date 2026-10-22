# Generic annotation preservation candidate

STATUS: WARN — implementation candidate; no qualifying execution yet.

Branch: `work/rel-generic-annotation-preservation-20261011`.
Base: `origin/release/1.0` at `f3eb9e8a4c8` when this lane was created.
Worktree: `C:/dev/simple-rel-generic-annotations`.
The transport commit is an unqualified candidate. No push or release admission
is claimed by this report.

## Evidence recovered from Claude

Session `75022ee3-ea0e-4bfe-bdb6-3d4b162cae8c` reported generics PR #2940,
merge `e89af76cf75`; it is an ancestor of this lane's release base. The report
explicitly distinguishes finite model testing from formal proof. Its local
`build/gen/full4.txt` also retains regression failures. It cannot qualify this
candidate: those tests used the Rust seed, and the native binary used by its
differential corpus predates the completed generics changes.

The checked-in instantiation model documents H-ANNOT: same-module `Bag<text>`
arguments were dropped before HIR. Text elements from a parameter field were
integer-added under a default warning. That implementation behavior motivated
this repair; warning-only handling is not accepted as completion.

## Candidate and checks

- Parser: reuse the existing instance registry for local and forward generic
  annotations, retaining ordered and nested arguments.
- HIR: retain invalid-argument diagnostics for locally resolved declarations.
  Unresolved imported-surface recovery is unchanged and remains an explicit
  limitation of the compiler, not proof of complete generic soundness.
- Mono: recursive template/argument matching compares nominal owner identities
  using the two symbol tables. The context-free model entrypoint retains its
  existing single-table interpretation.
- Four focused spec files cover annotation preservation, cross-module identity,
  parameter/result/local/field operations, and invalid local arguments.
- Native fixture:
  `test/fixtures/bootstrap/generic_annotation_fields/main.spl`, with exact
  expected stdout in `main.expected`.

Staged whitespace check passed. Working and staged runtime-facade and numbered
artifact guards passed, and `doc/06_spec` contained zero executable specs.
The full candidate has not been parsed, compiled, tested, or coverage-measured.
Neither the spec manuals nor a release verification PASS have been generated.
Independent source review found no obvious P0/P1; that is not execution proof.
`SymbolId`, `SymbolTable`, `HirType` and `HirTypeKind` are explicitly exported by
`hir_types.spl`, and the new table fixtures match its seven-argument `define`
signature. Imported classes use canonical owner/name allocation; imported
struct registrations rename their stored symbol to the original imported name.

Two existing binder limitations remain explicit: an argumentless nominal pattern
returns true without owner checking, and the context-free API compares raw ids.
The production parameterized-template routes pass ownership context, but this
does not establish general H-NAMED soundness: specialization keys still spell
nominal types by unqualified name. Those separate gaps must remain open.

## Required next verification

1. Review the entire candidate against the stated requirements and imported
   class/enum/trait compatibility, including re-exports and aliases.
2. Run the four focused specs with an admitted self-hosted runtime and private,
   producer-bound caches. Confirm the pre-fix cases fail for their intended
   reason; do not substitute seed results for this evidence.
3. Build a successor containing the patch. Compile and execute the native
   fixture on LLVM and Cranelift with stub fallback disabled, checking stdout.
4. Run the required compiler/lib/MCP checks, native smokes, SPipe manual gates,
   runtime-facade guards and commit/layout guards before landing.

The known diagnostic successor (`b580919372e209ea2a10e6d8e919b0f90c5dc3100e76f958f584c5db0ace4778`)
can native-build bounded probes but is not an admitted general test runner. No
probe using it has been run in this lane.

Other generic obligations remain separate: H-NAMED specialization-key collisions,
H-RET32 cross-module return ABI, H-XMOD mixed nominal ownership, lambda/visitor
coverage, and a production refinement argument beyond reduced substitution laws.
