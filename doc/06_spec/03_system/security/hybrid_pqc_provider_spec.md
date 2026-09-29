# Pure-Simple hybrid-PQC provider

**Status:** PARTIAL/RED — executable scenarios pin TLS and SSH profile names,
group, lengths, component order, secret sizes, authentication/AEAD requirements,
and terminal downgrade behavior. A deterministic pure-Simple ML-KEM-768
keygen/encapsulate/decapsulate exchange now checks all four pinned output digests
and exact 1184/2400/1088/32-byte boundaries. Independent implementation
differential, malformed-decapsulation corpus, ownership audit, and live
handshake oracles remain unresolved. Physical CUDA forward-NTT evidence now
covers two GPUs and 30 samples at each batch size, but remains deliberately
non-promoting because it is a narrow C oracle rather than full pure-Simple
ML-KEM execution.

The measured first sustained GPU wins are batch 3 on the RTX A6000 and batch 8
on the TITAN RTX. Batch 1 loses on both devices, so production policy continues
to select the pure-Simple scalar backend until full-operation evidence exists.

The current scenarios validate the pinned X25519MLKEM768 profile, exact wire
lengths/order, one deterministic pure-Simple ML-KEM exchange, terminal
downgrade policy, and checked CPU fallback. The unresolved release scenarios
must additionally validate FIPS 203 vectors through an independent oracle,
malformed-input implicit rejection, transcript/key-combiner behavior, secret
lifetime, and the pure-Simple ownership boundary. Scalar remains the
correctness owner. SIMD/GPU providers may be admitted only after full-operation
oracle parity and a measured crossover; the present forward-NTT-only receipt
does not satisfy that gate.

**Executable SPipe:** `test/03_system/security/hybrid_pqc_provider_spec.spl`
