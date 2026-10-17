# Preserve enum scalar nil words at the codec runtime boundary

Status: provisional implementation, NOT runtime-qualified. Bug database entry
pending qualified tooling. Do not treat this commit as deployment approval.

A174 assigns an i64 carrier to nil-first conditional bool/text decoder locals,
then rejects their enum construction against the declared scalar field type.
Ordinary bool extraction also collapses the nil word, so accepting the operand
or casting it to bool would not preserve the existing wire format.

The generator now constructs the actual typed variant, decodes present bool/text
normally, and records absent scalar slots. Only absent slots invoke the trusted
enum-wire SFFI boundary introduced in 2b0fe4e6db0. That boundary derives the real
identity from the typed prototype and copies multi-field payloads into a fresh
tuple before reconstructing the enum. It never changes an interned prototype,
guesses discriminants, or relaxes ordinary constructor validation. Encoding
checks raw nil slots before writing bool/text through budgeted writer methods.
Struct scalar encoding is unchanged; this is not a claim to repair every ABI.

The generator reserves nil-slot array storage before its allocation; the
restoration helper separately charges additional enum/tuple/result work and
storage. Errors invalidate the reader and return nil, never the placeholder
prototype as a successful decoded value. Present-only frames return their
actual typed prototype without reconstruction.

Generated synchronization was mechanical from the reviewed template and actual
schema descriptors: 34 encoder scalar sites, 34 decoder scalar sites across 33
variants. The final 33 pre-allocation reserves were synchronized mechanically
as well. Official generator regeneration/freshness verification remains pending.

Qualification evidence is external under phase3-validation-20261016:
manual-enum-wire-contract-cycle1 rejected an inline tuple payload; 502f43a96e9
replaced it with a typed local without dropping assertions. Cycle2 hit its8GiB
cap. Final cycle3 completed HIR (51 cache hits) and passed that tuple rejection,
but failed on the older producer's comment-only module eligibility check.
Zero retained objects, no executable, no assertions executed. All three probe
attempts are exhausted. Neither codec roundtrip nor generic FFI return ABI has
been proven. Full compiler generation is a separate prerequisite, not a renamed
fourth probe. The retained A174 executable and caches remain unchanged.
# Review follow-up

The reconstruction facade now copies all payload words once and then replaces
each requested nil slot once. Work is O(arity + slot count), matching the
reader work charge; repeated slots retain the same result. Every tuple write
still checks failure. Source review and whitespace validation only; native
qualification remains pending. Workaround implementation: 405e0968b9d069f9f4eea1ddc1b12c7afcbeb49a.
Intended-code recovery reference: 5c3e501759ae833a828b14b4e23c9238c73b76a6.
Bug database reconciliation remains pending qualified tooling.
