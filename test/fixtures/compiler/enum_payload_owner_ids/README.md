# Cross-module declared enum payload identity reproducer

Native UNRUN. Use an isolated admitted source root for this fixture; root src/
contains app.payload_provider, app.main and app.wrong_owner. Compile entries
separately with entry-closure and the same producer/options/runtime. Do not mix
this app namespace into the repository's app root.

Positive main.spl requires compile0/run0 and exactly
`enum payload owner identity: 5 checks, 0 failures`. It distinguishes provider
construction from consumer construction of Array/Dict payloads containing the
same imported Atom. The zero-length imported Array still has declared Atom
provenance. No casts, Any, explicit primitive representation or renamed enum
variants hide a nominal mismatch.

Negative wrong_owner.spl must be rejected for Array[WrongAtom] versus the
provider's Array[Atom] at its Packet.Items call. It must not pass merely because
an unrelated parser/import/toolchain failure occurred. Nonzero alone is not an
oracle; retain the exact typed diagnostic and qualified owner metadata.

A positive compile failure can precede runtime controls, so its diagnostic
must identify constructor versus extraction failure. Collection extraction is
addressed separately by263fa942efb (integrated604872eeb05). Foreign payload ID
remapping remains under investigation, not fixed by collection markers. The
current3bd producer lacks263fa; a failure from that producer cannot qualify the
collection repair or independently assign every symptom to nominal identity.
