# Positioned descriptor authority for bootstrap verification

## Implemented scope

The non-procfs authority-map ingress in the Stage 3 verifier now uses a retained
numeric descriptor and positioned reads. Linux keeps its existing procfs path.
This is a foundation for macOS and BSD verification, not full portable admission.
No runtime, product test, or full bootstrap result is claimed.

## Read contract

The shell opens map descriptor 9. The byte-bound verifier module contains an
isolated Python reader (`-I`) that performs `os.pread`, never a `/dev/fd` or
pathname reopen. Initial sealing verifies that the source pathname is regular
and its device/inode/mode/size/timestamps match the open descriptor before and
after the read. A symlink, replacement, short read, or mutation rejects sealing.
Each accepted read captures fstat before and after, compares device, inode,
mode, size, mtime and ctime, and emits bytes only after all checks pass.

The seal binds device, inode, mode, size, and SHA-256. Subsequent reads require
that same seal, independently of the shared seek offset. A later unlink or
pathname replacement cannot redirect the retained authority. An identically
sized rewrite or replacement descriptor fails content or identity binding.
The map is bounded to 1 MiB; oversized maps and nonregular descriptors fail.
The expected canonical map has 184 or 185 lines, well within that bound.

Map key lookup rejects missing or duplicate keys. Role order, line count, vector
hash, and whole-map hash consume the same sealed descriptor. Existing map,
manifest, tool, parent, and source checks continue to decide admission.
Repeated positioned reads rehash a small map to establish that every lookup
consumes the original bytes; this is an explicit integrity cost in the admission
path, not a runtime request handler. No shell sleep or retry loop is introduced.

## Interpreter and helper authority

Python 3 is an explicit prerequisite on hosts without procfs. The tool snapshot
producer includes its requested/canonical paths, executable SHA-256, version,
and architecture. The verifier pins the canonical interpreter path and digest
at ingress. After validating the map roles it requires exactly one recorded
Python row with that path and digest, and rechecks the executable hash. The
existing manifest verifier later regenerates the full tool snapshot and compares
it byte for byte; the snapshot hash remains bound to the map and manifest.
There is no exact tool-row count in this path. Existing admissions lacking
Python require new receipts; missing authority is not silently grandfathered.

The reader implementation remains embedded in `manifest-verify.shs`, whose
bytes are included in the existing helper bundle fingerprint. There is no new
production helper file or source import outside that bundle. The standalone
Python file under `scripts/check` is test-only. Isolated Python mode excludes
ambient PYTHONPATH and user site configuration.

## Focused evidence

Twelve targeted tests passed across three scoped invocations. They exercise
repeated reads with unchanged seek offsets, unlink/replacement, symlinks,
wrong/closed/directory descriptors, content mutation and mutation during reads,
key lookup, duplicate keys, vector hashing with trailing newline, helper byte
binding, and Python tool-authority rejection. The real Darwin verifier accepts
the map read boundary and rejects a forged status at `manifest-stage-map-status`;
it formerly failed earlier at `manifest-entry-bound-map-hash`.

No full bootstrap was run. The existing three-cycle session cap remains in
force. Shell syntax and diff formatting were checked for the initial foundation.

## Remaining integration

The manifest snapshot still uses descriptor 8 through Linux procfs, map-role
identity uses GNU `stat -Lc`, runtime directory handling uses descriptor 6, and
parent/source/helper descriptor transport in the shared runner and provenance
verifier remains Linux-specific. Capsule mode is not converted or bypassed.
These boundaries must adopt an equally bound protocol before a source-matched
macOS runtime can be admitted. This component alone cannot satisfy those gates.
