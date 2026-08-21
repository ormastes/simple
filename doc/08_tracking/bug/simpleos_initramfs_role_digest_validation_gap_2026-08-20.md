# SimpleOS initramfs role/digest validation gap

Status: open; static module closure implemented, runtime executable verification remains release-blocking

The packer now stages and hashes distinct compiler, interpreter, and loader
roles, emits their exact guest paths and digests in `SYS/SIMPLETOOL.SDN`, and
validates those bindings against the archived payload bytes. The pure-Simple
validator bounds zstd input and output, parses newc structurally, rejects unsafe
paths and unsupported link/file shapes, and fails closed on duplicate, missing,
renamed, or tampered role payloads.

Source closure is implemented by `src/os/port/initramfs_validate.spl` and its
behavioral archive spec. Release evidence is still blocked until the admitted
self-hosted Simple runtime executes that spec and the canonical target-image
and in-guest toolchain gates. Sequence-compressed zstd blocks remain rejected;
the packer emits bounded raw/RLE blocks until an output-capped pure decoder is
available.

The strict module boundary is now explicit. `cpio_newc.spl` exports only
`CpioEntry` and the fail-closed, resource-capped `cpio_parse_bounded` result
surface for structural archive consumers; malformed input never returns a
successfully parsed prefix. `smf.spl` owns
canonical EOF-128 header parsing and exports a narrow `Result`-based admission
facade for explicit SimpleOS executable envelopes. The initramfs validator no
longer imports `SmfHeader`, parses SMF offsets itself, or reads private header
fields. Runtime compilation and execution evidence remains deferred by the
no-runtime constraint of this implementation lane.
