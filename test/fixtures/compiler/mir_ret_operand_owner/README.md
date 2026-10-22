# MIR return operand owner (#3036)

The executable fixture calls real MirBlock return accessors for nil/non-Ret,
Copy/Move, every constant variant, and both Bool values. Require exit 0 and
`mir-ret-operand-owner: pass`. Object compilation alone is not execution proof.
Use the admitted pure-Simple producer with SIMPLE_NO_STUB_FALLBACK=1 and pinned
source/runtime identities. Native qualification is pending.
