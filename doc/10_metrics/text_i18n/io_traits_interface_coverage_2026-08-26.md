# I/O traits interface coverage classification — 2026-08-26

`src/lib/common/io/traits.spl` contains trait declarations and documentation
only. It has no executable decisions, so branch coverage has a zero denominator.
Reporting “100% branches” for this file would be vacuous.

The coverage contract schema is upgraded to `text-i18n-owner-coverage-v2` and
pins 29 executable branch owners plus one interface-contract owner
(`io_traits`). Executable owners require 100% measured branches. The interface
owner requires implementor conformance and behavior evidence.

The manifest contract spec passes 3/3 and fails closed for count, missing paths,
duplicates, invalid classifications, and backend evidence. Existing real
implementors include `FileHandle`, `BufferedReader`, `BufferedWriter`,
`TcpStream`, `Stdin`, `Stdout`, and `Stderr`; buffered-reader tests exercise
valid line decoding and malformed-byte replacement through `Read`.

The dedicated method-complete conformance spec
`test/01_unit/lib/common/io_traits_interface_contract_spec.spl` also passes
3/3. Its in-memory implementation exercises byte/text read and write, exact and
short reads, all three seek origins, rewind/position, negative input, flush,
close, and every post-close rejection across `Read`, `Write`, `Seek`, and
`Close`.

This does not waive I/O performance requirements. Concrete streaming readers
and decoders still require latency, allocations, copied/transient bytes,
steady/peak RSS, decoder-state bytes, and post-close retention.
