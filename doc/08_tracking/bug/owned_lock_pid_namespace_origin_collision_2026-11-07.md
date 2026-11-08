# Owned lock origin can collide across Linux PID namespaces

Severity: P1. Source repaired; authored native evidence **NOT_RUN**.

The original pre-gate process-origin guard compared only numeric getpid values.
A parent that is PID 1 can fork the first child of a new PID namespace, also
PID 1. That child can inherit the parent's held registry gate and generation
tokens. Numeric equality then permits it to spin on the stranded gate instead
of refusing before any lock or native ownership access.

The canonical included `runtime_file_lock_owned_v2.c` now establishes PID plus
a verified native PID-namespace device/inode pair. The first observation opens
`/proc/self/ns/pid`, checks fstat, nsfs filesystem magic and the kernel namespace
type, and checks close exactly once. Later observations use stat only. Initial
publication is guarded by a lock-free atomic phase; incomplete publication
refuses immediately. No established origin or inherited gate is reset.

After publication, PID mismatch, namespace mismatch or observation failure
permanently quarantines the copied process owner. Restoring proc visibility or
the original stat result cannot re-enter its held gate. Guard calls preserve
errno, do not allocate and do not open or close descriptors on an established
foreign/uncertain path. Checks run before the gate, every 64 contended spins,
and immediately after successful acquisition. A failed post-check leaves the
quarantined gate untouched; it is not an unlock/recovery port.

Acquisition already has a uniquely reserved slot while opening/polling outside
the registry gate. If origin is lost after an actual handle opens, that thread
publishes the local native handle into its reserved slot and release-publishes
atomic phase UNKNOWN, returning the existing generation token. It performs no
foreign gate acquisition, unlock, close, or raw descriptor retry. Positive
state/release calls with a refused origin return conservative UNKNOWN instead
of dropping the owner as stale. A failed open has no native resource to hide.
One atomic phase snapshot prevents a concurrent acquiring-to-UNKNOWN transition
from falling through a release path into native close.

Five authored Linux cases include actual ordinary successful acquire/release,
then cover real PID1-to-PID1 namespace collision, restored
stat failure, restored inode mismatch and post-poll origin loss retaining an
actual contended lock. They require real user/PID namespace support and have
not been compiled or executed. Namespace denial is blocking/failing evidence,
not a skip or passing emulation. Existing ordinary fork expectations now retain
UNKNOWN ownership instead of claiming a stale/closed native resource.

This is not general async-signal/fork safety inside a native critical section
or a native open/poll call. Root retains the existing no-fork-inside-operation
contract. The periodic stat check adds bounded-frequency syscall work during
contention; this change claims no measured latency or throughput result.
