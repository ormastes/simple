# Complete semantic type identity transport V1

Accepted-plan link: [type consistency, section3.2](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md).
Source baseline: `53419f623a540659087f2ad8e925349dcbbbf7a4`.
Status: common contract/validator/specs authored; runtime verification pending.
<!-- codex-architecture -->

`compiler.common.data.data_semantic_type_identity_v1` is a pointer-free
transport/equality contract for the existing semantic type owner's projection.
It does not resolve names, expand aliases, issue owner authority, prove that a
type checks, or replace the canonical data-schema resolver. The separate HIR
adapter and V3 resolver consume it; this independent dependency is not full W1.
Frozen V1/V2 nominal paths/arguments/digests are not repurposed.

## Contract and complete framing

`DataSemanticTypeIdentityV1{version,canonical,byte_len}` carries a complete
structural descriptor, not a hash or process-local TypeId. `byte_len` is checked
against UTF-8 bytes. Exact comparison validates both descriptors and compares
their entire canonical texts. A caller's digest bucket is never type proof.

A node is `LP(tag) count(fields) LP(field)* count(children) LP(child-node)*`.
`LP(x)` is the canonical decimal UTF-8 byte length followed by `:` and x.
`count(n)` is canonical nonnegative decimal followed by `:`. Leading zeroes,
truncation, non-decimal counts, unknown constructor/version, wrong arity,
non-roundtripping UTF-8 boundaries and trailing bytes are rejected. Every child
frame must be consumed exactly. There is no ignored suffix or partial identity.

| Constructor | Fields | Children |
|---|---|---|
| int / float | width,signedness / width | none |
| bool,char,text,unit,never,any | none | none |
| named | canonical terminal module,name,kind | recursive generic arguments |
| dyn | canonical terminal module,name,trait | none |
| array | exact nonnegative size or `?` | element |
| ref / ptr | immutable or mutable | referent |
| slice,optional,isolated,unique,shared,weak | none | inner type |
| dict / result | none | key,value / ok,error |
| tuple / union | none | owner-supplied ordered members |
| function | parameter count,effect count | parameters,result,sorted unique effects |
| effect.pure/io/async/mutates/allocates | none | none |
| effect.throws | none | thrown type |

Effects cannot occur in ordinary type-child positions or at the descriptor
root. Nominal kind is struct/class/enum/trait; an unresolved alias is not a
terminal nominal constructor. Semantic owners supply alias expansion and exact
terminal provenance before projection. Structural validity alone cannot turn
an arbitrary SDN spelling into a bound semantic declaration.

## Bounded cold work

Admission bounds are 65536 UTF-8 bytes, depth32, 1024 aggregate nodes, 16 fields
per node and 256 children per node. Numeric framing bounds are checked before
multiplication; function counts are bounded before summation. The bounded
packer computes complete framed byte cost before assembling a semantic node.
The raw packer remains a fixture/codec primitive and does not admit a key.

Validation is per frozen schema/context, not per attribute read/write. It has
no filesystem/process/environment access, mutable cache, hash registry or
separate nominal-name table. Work is bounded by descriptor size/depth; recursive
frame decoding creates transient byte/text arrays. No latency/RSS/allocation
target is claimed measured. Identity version or canonical bytes changing must
invalidate a consuming V3 schema/context; physical layout/profile identities
remain separate.

## Evidence and completion boundary

Seven authored cases cover nested qualifier distinctions, nominal owner/name/
kind distinctions, Unicode byte lengths, malformed framing/versions, arity and
effect placement, depth/node budgets, and exact comparison within a forced
shared digest bucket. The manually authored companion is under `doc/06_spec`.
No interpreter/native test, generated manual maintenance, branch coverage or
compiler/MCP smoke PASS exists yet. These gates require the exact admitted
producer and remain pending after source-only review/landing.
