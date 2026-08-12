enum extension = { Ext_Zca }

let xlen : int = 64
let base_E_enabled : bool = false
type regidx_bit_width = 5
newtype regidx = Regidx : bits(5)
newtype cregidx = Cregidx : bits(3)
let zreg : regidx = Regidx(0b00000)
let ra : regidx = Regidx(0b00001)
let sp : regidx = Regidx(0b00010)

function currentlyEnabled(_ : extension) -> bool = true

mapping encdec_reg : regidx <-> bits(5) = {
  Regidx(r) <-> r
}

mapping encdec_creg : cregidx <-> bits(3) = {
  Cregidx(r) <-> r
}

scattered union instruction
val encdec_compressed : instruction <-> bits(16)
scattered mapping encdec_compressed
