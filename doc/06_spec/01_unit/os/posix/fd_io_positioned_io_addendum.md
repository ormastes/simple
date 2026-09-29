# POSIX positioned-I/O compatibility addendum

The generated `fd_io_route_spec.md` manual remains the canonical record for
the established routing scenarios. This addendum records the bounded
positioned-I/O migration without replacing that generated evidence.

`posix_pread_exact_bytes` no longer implements positional reads by changing the
shared open-file-description offset, calling sequential `read`, and restoring
the saved offset. A connected positioned provider reads the requested range
without observing or mutating that shared cursor. If the older generic kernel
route cannot provide the generation-bearing registered buffer required by
SOSIX filesystem v1, it fails closed with `-EOPNOTSUPP` (`-95`) and likewise
leaves the offset unchanged.

The canonical FAT32 service route remains available and cursor-independent:
`SosixFat32PositionedBackendV1` delegates to
`SharedFat32Driver.read_at/write_at`. The focused executable spec adds one
successful positioned-read case and one unavailable-provider case; both assert
that the descriptor offset remains unchanged.

The single focused interpreter run did not compile the specification because
of an unrelated parser failure in `src/os/sosix/fs/ipc_codec_v1.spl`
(`expected LParen, found Dot`). It executed zero examples, so this addendum
does not claim a passing test result.
