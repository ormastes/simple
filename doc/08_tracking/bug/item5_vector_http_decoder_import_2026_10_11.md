# Vector HTTP parser omitted its decoder import

The de400 source compiled by Phase2 `75c28d4a1451385f2c4656d1d8a17a3b21d0e1e99126b56ef6bf4c484b794a51`
failed its real HTTP vector app build with three `unresolved name: bytes_to_text`
errors in `vector_parser.spl`. Evidence is retained in
`apps-release-20261010-attempt2/http-vector/build.log` on the Item5 ext4 volume.

Import the existing `std.common.base_encoding` facade decoder explicitly for
request-line, header and body conversions. Preserve that facade's existing
decoding behavior; this change does not switch to the different replacement-byte
policy of the utilities decoder or alter configured HTTP parser selection.

`http_vector_utf8_line_boundary.spl` imports the actual parser module and checks
a UTF-8 code point split across chunks, CRLF framing, exact decoded text and the
unconsumed next byte. The existing live-socket vector app remains the full
request/header/body and provider admission regression.

Status: source repair and assertion fixture authored; native execution pending
the root-owned rebuilt compiler. No runtime, performance or release PASS claimed.
