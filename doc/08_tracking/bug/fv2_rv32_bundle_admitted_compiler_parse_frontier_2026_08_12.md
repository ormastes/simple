# FV2 RV32 bundle admitted-compiler parse frontier

## Status

Open until a current-source pure-Simple compiler admits the bundle generator.
The three-cycle cap was reached; no fourth compile was attempted.

## Evidence

Building `src/app/verify/riscv_add_formal_bundle.spl` with the admitted
pure-Simple LLVM compiler advanced through three deterministic discovery
frontiers:

1. `riscv_scalar_product_to_vhdl.spl`: multiline value conditional followed by
   a same-line `else`;
2. `riscv_scalar_product_composition.spl`: result type split after `->` and a
   semicolon-combined statement;
3. `riscv_scalar_csr_owner.spl`: another multiline conditional with same-line
   `else`.

Current source now spells each form with explicit line/indent ownership. The
bundle entry also uses canonical file/directory facades and `char_code_at`
identity validation, avoiding the known corrupt native `for ch in text` path.

The end-to-end shell owner now builds its generator with
`SIMPLE_NO_STUB_FALLBACK=1`, captures and scans the transcript, and promotes a
temporary executable only after rejecting stale-runtime and stub markers.

## Required closure

1. Admit the current-source compiler from the already-running bootstrap lane.
2. Build the generator once with that compiler and require a clean transcript.
3. Execute proof, reachability cover, subtraction mutation, RTL/netlist
   equivalence, and pinned Sail differential jobs over one exact bundle.
