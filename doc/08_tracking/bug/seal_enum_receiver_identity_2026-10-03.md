# Seal enum receiver identity — candidate investigation

Status: native verification pending; this is not a closed failure family.

The Ubuntu diagnostic used source `43f626850b6a5531e89110f75cd1eaedc24adcd1`
and producer SHA-256
`e58968bba401407bb04d6b581e62cf1dcf480847ec56338bb7a06ad4003283ff`.
The catalog is `D:/dev/ubuntu43f-failure-catalog-20261003/evidence.json`.
Its attempts are diagnostic, with `canonical_admission=false`.

## Observations

- U43F-002/003/008/015 first reject `SdnValue.get` from the manifest closure.
  Further errors include `as_str`, `as_array`, `as_i64`, `as_dict`, missing
  enum constructor owners, and ambiguous bare enum variants.
- U43F-016 first rejects `IdentityError.code` on the `IdentityRejected(inner)`
  payload in `seal_error_code`.
- MIR unresolved instance dispatch previously required a
  `struct_value_syms` entry before consulting the receiver's declared type.
  Enum parameters are excluded from the struct-layout registration path.
- Single-field enum extraction computes `effective_payload_type` but did
  not retain it on the extracted MIR local for subsequent method lookup.

These are concrete source gaps, not proof that they explain every diagnostic.
The constructor/variant errors and SDN container operations need separate
verification; the global dictionary repair is not assumed to cover them.

## Candidate

Retain the extracted payload's HIR type. When unresolved instance lookup has
no struct owner, recover a declared enum owner only if its symbol is an Enum
and its qualified identity is registered. Reuse existing instance-call
lowering, including receiver arguments and default argument handling.

## Regression evidence required

`test/fixtures/native_enum_receiver_identity/main.spl` imports its owner
module and checks an enum parameter method, two nested enum payload variants,
and the enclosing enum's no-payload alternative. Compile with the fixture
directory as a source root and this file as the entry. Successful execution
must print `enum receiver identity: PASS` and exit zero; failures exit 11–14.

Run the baseline probe with the pinned producer before interpreting the
candidate result. A fixture already passing on the baseline is coverage,
not a reproduction. Verify the candidate with a rebuilt self-hosted producer,
then rerun the exact manifest and seal closure entries from the catalog.
Use a Linux-owner-reserved guarded slot; do not modify frozen source or reuse
old producer evidence as proof of a newly edited compiler.

Static `git diff --check` passed. No native test or full verification PASS is
claimed. Compiler/core smoke, env audits, and regression execution remain
pending before landing.
