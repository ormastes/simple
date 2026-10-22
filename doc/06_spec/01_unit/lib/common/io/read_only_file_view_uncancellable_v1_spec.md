# B5 Cycle 2: descriptor-bound uncancellable buffered reads

Status: authored tests-first manual; execution and doc generation **UNRUN**.

Executable owner: `test/01_unit/lib/common/io/read_only_file_view_uncancellable_v1_spec.spl`.
This manual describes real filesystem assertions. It contains no executed PASS claim.

The additive API under test is
`read_only_file_view_read_buffered_uncancellable_v1(view, offset, length)`.
It borrows an existing pinned view, requires its policy to be `buffered`,
checks the original file range and the view's address-space budget as an
explicit byte limit, and returns the pinned descriptor's owned bytes and
identity. The caller retains close ownership after success and failure.
This new contract leaves the existing cancellable APIs unchanged.

| Scenario | Action | Required observation |
|---|---|---|
| Path replacement and restoration | Create distinct same-length A and B files, pin A, rename A aside, move B onto A's live pathname, read while B is visible, restore both paths, then close. | The actual live path contains B during the read. Returned bytes hash to A and differ from B; the returned identity equals pinned A. The restored live path contains A and the saved descriptor is invalid after close. |
| Exact offset and empty file | Read three bytes at offset one with a three-byte budget; separately open a real empty file and read zero bytes. | The interior payload is `AAA` with offset one and length three. The empty file yields zero bytes and size zero. Both views close successfully. |
| Bounds and capacity | Request a valid file range above the explicit budget, a range past EOF, and an overflowing offset; then request a valid bounded range. | Each invalid request returns `invalid_range`; the subsequent valid read returns original bytes. Close succeeds once, a read afterward returns `closed`, the actual descriptor becomes invalid, and a second close fails. |
| Buffered-only policy | Open the file with `prefer_map`, call the new API, then close. | Reading returns `mapping_unsupported`; closing succeeds. |
| Actual inode size change | Open a file, append to that same file through the existing positional-write owner, read the original range, then close. | The write succeeds, reading returns `identity_changed`, and close releases the actual descriptor. |
| Existing cancellable behavior | Cancel an actual registered token and request an invalid range through both original buffered and view APIs; then read valid ranges with another actual uncancelled token and close. | Both cancelled calls return `cancelled` before range validation. Both uncancelled calls return original pinned bytes. Close succeeds and each registered token retains its actual cancellation state. |
| Cancellation registry stability | Allocate a valid registered token, perform 64 actual reads from one pinned view, close, then allocate another valid token. | Every read returns exact original bytes. Both explicit tokens are valid and uncancelled; the second token's ID is exactly the first plus one. The reader allocates no intervening tokens. |

The path-swap case preserves A's actual inode using filesystem rename; it does
not reconstruct A by writing its spelling again. Fixture writes occur before
the descriptor is acquired. After acquisition, assertions that can fail are
deferred until path restoration and descriptor close have been attempted.
The tests invoke the production read owner directly, with no alternate
toolchain, injected descriptor identity, fake cancellation token, or mocked
positive result. Unsupported platforms remain visible execution failures
until a qualified backend is admitted.
