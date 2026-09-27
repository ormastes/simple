# Positioned descriptor authority for bootstrap verification

## Implemented scope

The non-procfs authority-map and manifest ingress in the Stage 3 verifier use
retained numeric descriptors and positioned reads. Role identity and content
checks use held descriptors. Linux keeps its existing procfs path.
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

## Retained manifest and role identity follow-up

The verifier seals manifest descriptor 8 with the same positioned-read contract.
All key reads in the verifier dispatch through `bootstrap_stage3_verify_value`;
reads of the retained manifest use its descriptor and seal. Other receipts and
the Linux branch retain the existing key lookup helper. No manifest key lookup
reopens its source pathname after sealing. Unlink or replacement therefore
cannot redirect a later read; mutation of the retained content rejects it.
The portable path does not require an on-disk mutable snapshot or shared-offset
`/dev/fd` reads. The existing Linux snapshot branch remains in place.

Role identity checking on non-procfs hosts opens the role using `O_NOFOLLOW`
and `O_NONBLOCK`, adding `O_DIRECTORY` for directory roles. Before-open lstat,
after-open fstat, final fstat, and final lstat must agree. File contents are
hashed through the held descriptor; no separate pathname hash/stat race is
introduced. Device, inode, and permission/special mode bits must match the map.
The mode is parsed as octal and compared with `stat.S_IMODE`; a Darwin test
compares it directly with BSD `stat -f %Lp`. File roles also require the exact
recorded SHA-256. Wrong type, symlink, replacement, or mutation rejects authority.
The expected output is checked through this same role boundary.

Seven additional focused tests passed, including replacement/mutation during
role hashing, wrong identity/digest/type, exact mode semantics, manifest reads
after pathname replacement, retained-content mutation, and existing lookup
behavior on the nonportable dispatch. A complete 184-line authority-map fixture
with real file identities passes the real Darwin role and interpreter checks,
seals a manifest, and fails at `manifest-status-not-singular` as expected for
an intentionally incomplete manifest. This is no claim of full admission.
The initial six-test follow-up took 8.6 seconds, dominated by interpreter process
startup for repeated sealed-map key reads. Shell syntax and diff checks passed.

## Portable authority-map producer follow-up

The map writer now shares `role_snapshot` with the verifier on non-procfs hosts.
One held descriptor supplies device, inode, octal permission/special mode bits,
and file digest. The primitive verifies regular-file or directory type, uses
no-follow opens, and requires source lstat and held fstat identity to agree
before and after the read. It returns no receipt when content or identity
changes during capture. Directories emit no digest, matching the existing map
schema. Linux retains its original GNU stat/hash branch and receipt shape.

The existing row emitter and map-publication sequence are factored into callable
production helpers. Each row now propagates failure explicitly. A failed first,
middle, or final role removes the partial temporary map before publication.
The schema, ordered roles, optional backfill form, vector digest, exclusive
publication link, and read-only final mode remain unchanged. Python preparation
and canonical interpreter pinning are shared by producer and verifier; the
implementation remains within the existing byte-bound helper bundle.

Five new targeted tests passed on Darwin in 3.7 seconds. The production map
publication helper emits both the 184-line absent-backfill and 185-line
present-backfill forms with 31 roles, correct vector digests, and mode 0400.
Each emitted role is independently compared against OS stat/content and accepted
by the portable verifier primitive. Missing first/middle/last inputs leave no
published map or temporary file; symlinks reject; mutation during capture emits
no receipt. Shell syntax and diff checks passed. These fixtures exercise real
map generation without constructing an admitted compiler or running bootstrap.

## Remaining integration

The runtime directory descriptor-6 branch, parent/source/helper descriptor
transport, and descriptor-capsule admission remain Linux-specific. The shared
runner and standalone provenance verifier need corresponding descriptor
transport support. Existing parent and source validation has not been disabled
or replaced. No full bootstrap or source-matched macOS runtime admission has
been performed.
