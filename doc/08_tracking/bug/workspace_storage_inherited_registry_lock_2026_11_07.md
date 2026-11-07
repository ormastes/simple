# Fork descendants inherited workspace storage authority and registry locks

Status: source repair and focused native regression in progress. This finding
affects the previously merged native workspace registry; the storage, mapping
and preparation component PASS records did not exercise fork-child isolation.

The shared owner in `src/runtime/runtime_workspace_storage_v1.c` used a static
pthread mutex without checking the creating process. A child forked while a
different parent thread held that mutex could wait forever. If the mutex was
unlocked, the child could reach copied storage slots and descriptors. Mapping
refresh's observer-thread identity check was later than mutex acquisition and
did not protect storage operations or mapping close.

The repair must atomically latch the native process identity before acquiring
any registry lock, reading tokens or causing native effects. On Linux, identity
includes the actual PID namespace device/inode: PID alone can collide when a
PID-1 parent creates a child that is PID 1 in a new namespace. A fork descendant
must refuse without resetting the mutex, reconstructing state, closing copied
descriptors or acquiring inherited locks. A process forked before the registry
was ever used can bind its own empty registry. Namespace observation errors or
an origin record still being initialized refuse rather than waiting or adopting
state. The immutable namespace pair is read only after its atomic publication.
Serialized receipts still confer no authority.

After identity is established, a failed or mismatching namespace observation
permanently quarantines that process-local registry. If proof is lost while a
mutex is held, the owner does not unlock without proof. Restoring `/proc` must
not permit a later entry to wait on that retained mutex: quarantine refuses
before lock access until process recovery. Native owners and host capacity
charges remain retained; this is not successful live cleanup.

Linux registry acquisition uses one trylock and reports contention as `EBUSY`.
It rechecks identity after acquisition. No thread queues indefinitely behind a
mutex that another caller may have to retain in quarantine. Existing Simple
owners retain leases/tokens on that refusal; initial admission refuses before
publishing a new native owner. Windows SRW contention policy is unchanged.

Preparation borrows two existing slots while hashing outside the registry lock.
Its busy flags are atomic. Completed work first copies every return field and
finishes every native/slot read, then validates both generations and loan states
before releasing the flags. No slot is read after release starts. This avoids
stranding a completed loan merely because the registry is busy at completion;
it does not release the native owner or discharge storage capacity. A lost
origin proof retains both loans and returns no success receipt.

Text refusal also must avoid `rt_string_new("", 0)`: that function takes the
runtime's short-string cache lock, which can independently be inherited locked.
The child-origin branch needs a valid nonallocating refusal representation.

The focused regression will fork while the real parent registry mutex is held,
invoke the public storage, user-observation and preparation entries in the
child under a finite timeout, and assert refusal without touching parent state.
The parent must retain its mutex/registry and remain usable afterward. A linker
allocation-call witness must reject any child call to `rt_string_new`, proving
that refusal never reaches the inherited runtime cache lock. This observes the
actual call boundary; it does not manufacture a successful owner. This
is a new owner-boundary test, not a rerun of the historical quota, mapping or
preparation component fixtures. No successful quota admission or Podman effect
is fabricated for this test. Actual namespace-clone setup remains unexecuted;
ordinary fork execution does not establish that platform scenario.

A separate deterministic syscall-fault case in the same new fixture injects
one `stat` failure during guarded mutex release, then observes that actual
namespace reads work again. The registry must still refuse immediately and
retain its mutex/state. This is injected fault prevention, not a claim that
the host's `/proc` actually failed during the run.

The additional loan-release concurrency case uses isolated local slot metadata
without native handles, quota admission or a fake public lease. It exercises
the real internal release primitive while another thread holds the real
registry gate, and checks generation/busy mismatches refuse both releases.
This is explicitly mechanism coverage; actual quota/keeper preparation remains
unqualified.
