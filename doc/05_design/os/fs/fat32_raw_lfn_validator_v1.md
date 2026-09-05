# FAT32 raw LFN validator v1

The kernel FAT32 directory scanner treats an LFN chain plus its immediately
following 8.3 entry as one fail-closed association. It accepts at most 20 LFN
slots and 255 UTF-16 code units. The first physical slot must carry LAST and
the highest ordinal; subsequent ordinals must descend without gaps to one.
Every slot must have attribute `0x0f`, type zero, cluster zero, and the same
checksum, which must equal the checksum of the exact following 11-byte alias.

Decoding proceeds in logical order with no per-fragment text copies. NUL may
terminate the name; every remaining unit must be `0xffff`. Surrogate pairs may
cross slot boundaries, but lone or reversed surrogates fail. Empty names,
forbidden FAT characters, control characters, trailing spaces/dots, and names
over 255 UTF-16 units fail. The associated short field must use contiguous
space padding and legal 8.3 bytes. A malformed LFN makes both its long name and
its following alias unreachable during that scan; it is never silently treated
as a bare alias. A malformed pending association also terminates that directory
scan, so corrupting an intermediate slot's attribute cannot resynchronize at
the real following alias and expose it as an unrelated bare entry.

The short-name validator accepts legal OEM bytes without guessing a code page,
preserving their raw byte identity for the mount presentation policy. A leading
`0x05` is decoded as the FAT escape for `0xe5`, while the association checksum
continues to cover the raw `0x05`. Attribute bits 6-7 and NTRes bits other than
the specified base/extension lowercase flags are rejected; lowercase flags are
applied bytewise only to ASCII `A..Z`, preserving opaque OEM bytes. Dot entries
must have the exact directory attribute, zero size, zero NTRes, and canonical
space padding; their parent-relative cluster semantics remain the caller's
directory-context responsibility.

Short-alias lookup uses the same ASCII-only fold; it never applies Unicode
case conversion to opaque OEM bytes. Validated LFNs retain Unicode-aware case
comparison as a separate path.

Lookup and directory listing share this validator. The change intentionally
does not issue executable identity: serialized directory identity publication
remains owned by the separate FAT32 executable-identity transaction.
