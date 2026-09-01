function oracle_hex_nibble(n : int) -> string =
  match n {
    0 => "0", 1 => "1", 2 => "2", 3 => "3", 4 => "4", 5 => "5", 6 => "6", 7 => "7",
    8 => "8", 9 => "9", 10 => "A", 11 => "B", 12 => "C", 13 => "D", 14 => "E", _ => "F"
  }

function oracle_hex16(v : bits(16)) -> string =
  oracle_hex_nibble(unsigned(v[15..12])) ^ oracle_hex_nibble(unsigned(v[11..8])) ^
  oracle_hex_nibble(unsigned(v[7..4])) ^ oracle_hex_nibble(unsigned(v[3..0]))

function oracle_emit(parcel : bits(16)) -> unit = {
  let prefix = oracle_hex16(parcel);
  if parcel[1..0] == 0b11 then
    print_endline(prefix ^ "\tnot-compressed\t--------\t4\tnot-compressed")
  else if encdec_compressed_backwards_matches(parcel) then
    print_endline(prefix ^ "\tlegal\t--------\t2\tzca-classification-only")
  else
    print_endline(prefix ^ "\tillegal\t--------\t2\tillegal")
}

function main() : unit -> unit = {
  foreach (i from 0 to 65535) {
    oracle_emit(to_bits_checked(i))
  }
}
