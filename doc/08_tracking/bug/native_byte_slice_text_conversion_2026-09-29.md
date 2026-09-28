# Native byte-slice to text conversion loses payload

Status: open runtime/compiler bug; blocks cold package archive member
validation in the Target 6 native publication spec.

An isolated two-unit no-stub native probe, built by the immutable Stage2
pure-Simple compiler capsule, evaluated `"abcDEF".bytes().slice(0, 3)`.
The slice reported length 3, but `validated_utf8_bytes_to_text_linear`
returned an empty string. Copying the same first three source bytes with
`push` into a fresh `[u8]` produced `abc` through the same converter. The
probe executable SHA-256 is
`ee3ebdede0f34300ba38252fd4196f38c552280f551874ce9d3a4ffd9bdc8cb4`;
its source remains at ignored
`build/mini_builds/target6_archive_slice_probe.spl` for diagnosis.

The product archive and receipt files have correct whole-blob and member
SHA-256 values when checked outside the runtime. The native cold publication
path uses `archive_content.bytes().slice(start, end)` before UTF-8 conversion
and reports a member digest mismatch. A preallocated copy trial did not fix
the four-example spec and was reverted. The runtime owner should isolate
whether slice views, preallocated byte assignment, or `rt_bytes_to_text`
lose the payload, add a permanent native regression, and repair the shared
operation. A local workaround must preserve bounded linear time and the
archive's maximum-byte policy; it needs the original publication spec and
paired RSS/latency proof before qualification.
