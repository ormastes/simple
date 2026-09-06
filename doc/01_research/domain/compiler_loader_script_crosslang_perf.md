<!-- codex-research -->
# Compiler loader script cross-language performance: domain research

## Negative lookup caching

Negative caching avoids repeating expensive lookup work, but its cache key and
invalidation rule are correctness properties. A caller-relative import cannot
share a key that omits the caller. A cache reset must invalidate both successful
and unsuccessful entries. The POSIX `stat` interface also makes clear why this
project describes its portable counter as failed facade probes rather than
syscalls: an implementation may satisfy a file-existence request through
different libc or operating-system mechanisms.

Source: [POSIX stat](https://pubs.opengroup.org/onlinepubs/9699919799/functions/stat.html).

## Packed byte collections

Mainstream runtimes distinguish packed bytes from general object collections.
Python documents `bytes` as immutable and `bytearray` as mutable byte sequences;
Rust's `Vec<T>` documents contiguous heap storage and clone/equality through
the element contract. These references support two local design choices:
packed bytes should preserve ordinary collection value behavior, and mutation
must respect mutability/aliasing rather than silently changing an unrelated
copy.

Sources: [Python binary sequence types](https://docs.python.org/3/library/stdtypes.html#binary-sequence-types-bytes-bytearray-memoryview),
[Rust `Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html).

## Foreign pointer lifetime

Rust's raw-pointer documentation treats dereference as unsafe and requires the
pointer to be valid and properly aligned. The Rust FFI guidance also places
ownership and lifetime responsibility on the boundary contract. A temporary
pointer derived from interpreter-owned packed storage therefore must be scoped
to the foreign call, bounded by a descriptor, and prevented from escaping or
being treated as writable unless the API explicitly owns write-back.

Sources: [Rust raw pointers](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html#dereferencing-a-raw-pointer),
[Rust FFI](https://doc.rust-lang.org/nomicon/ffi.html).

## Performance evidence

GNU `time` distinguishes elapsed time from maximum resident set size and
defines `%M` as maximum RSS in KiB. This supports retaining wall and RSS as
separate fields. Benchmark comparisons also require equivalent work, multiple
samples, explicit tool versions, and checksums so an optimized-away or failed
workload is not admitted. A timeout is a failure receipt, not a slow sample.

Source: [GNU time format](https://www.gnu.org/software/time/manual/html_node/Resource-Measurement.html).

## Applicability

These sources inform the requirements options; they do not select one. The
project additionally requires pure-Simple self-hosted identity and exact
provenance, which is repository-specific and stricter than the general domain
references.
