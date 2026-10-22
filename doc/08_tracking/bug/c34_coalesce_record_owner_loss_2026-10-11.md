# C34 null-coalesce record owner loss

Retained C34 serializer MIR evidence is at
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c34-producer-mir-json-fragments-attempt1/normalized-mir-errors.json`.
Frozen source: `20a93224b3f08a86a15b520252bd95965f1e6423`; producer:
`f00dbc9c608dfaf22a15736747799821ed1b75871bf45ad3fe1b133701030e81`.

Seventeen ambiguous enum-pattern diagnostics in `mir_instruction_graph.spl`
follow `val payload = value ?? mir_operand_const_int(0)` and matches on
`payload.kind`, sometimes followed by `const_value.kind`. The argument is a
declared `MirOperand?`; its inner record owns the enum field. Source tracing
shows the coalesce path recovers that inner record but records only its bare
name. It can allocate the merged result as erased I64, and at merge remembers
HIR types only for arrays/slices. Later field/match lowering therefore lacks
the record's declared owner. This supports a common cause; no rerun proves
that this repair resolves all seventeen diagnostics.

The scoped repair retains the optional's actual inner record HIR type and
registered composite layout key on the merged local. When the expression
has no result type, that record also supplies the MIR result type. A present
expression annotation must agree before this new metadata is recorded.
`has_type_` is authoritative: a nonnil placeholder with a false presence bit
does not count as an annotation, and Infer/Error annotations remain unresolved,
matching existing enum expression type recovery. Direct constructed-HIR specs
check false-presence Bool/Error placeholders and a present Error annotation,
asserting both the merged HIR owner and MIR Struct owner remain the declaration.
The live fallback is checked against the same declared record owner using
existing payload compatibility; a different or unproven owner is fatal.
A terminated fallback needs no value check. The default is still lowered
only in its else block and evaluated only at runtime on absence.

No scalar/array/dictionary policy is broadened and no enum discriminant is
selected by spelling. Imported struct-pattern registration and the two
tuple-match diagnostics at `mir_fold_binop` remain separate investigations.

Authored SSpec runs real frontend/HIR/MIR lowering with colliding enum variant
names and a negative fallback owner. The standalone
`test/fixtures/compiler/optional_record_coalesce_owner/main.spl` adds physical
import owners, a text field before the enum field, Some/absent results, and a
counter proving lazy default execution. Expected exit is 0. Its
`negative_owner.spl` must fail compilation and produce no artifact.
Use entry closure with the fixture directory and matching admitted compiler
sources; preserve private phase/producer/source-bound caches. No builds or
runtime tests were run for this source-only candidate. Qualification and
independent review remain pending.
