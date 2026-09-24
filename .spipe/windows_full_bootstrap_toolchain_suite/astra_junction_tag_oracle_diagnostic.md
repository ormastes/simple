**The defect is the independent oracle’s signed/unsigned comparison**, at [test line 100](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:100). Line 87 starts the failing PowerShell invocation.

- `[BitConverter]::ToUInt32($b,0)` returns unsigned **2684354563** for a junction. Windows PowerShell interprets bare `0xA0000003` as signed `Int32` **−1610612733**. These compare unequal. Casting that negative literal directly to `[uint32]` can fail; use `[uint32]2684354563`.

- **Layout is correct.** `REPARSE_DATA_BUFFER` has `ReparseTag` at byte **0**, length at **4**, reserved at **6**, and union data at **8**. Windows little-endian junction bytes are **03 00 00 A0**. The oracle reads the correct bytes. Separately, `FILE_ATTRIBUTE_TAG_INFO` stores attributes at offset 0 and tag at offset **4**; the [producer’s two-uint structure and query](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:201) correctly use that different layout.

- **Native creation/validation are consistent:** [producer lines 307–320](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:307) construct the mount-point buffer, write unsigned `0xA0000003u`, and call `FSCTL_SET_REPARSE_POINT` (`0x900A4`) with the complete input buffer and null/zero output. [Validation](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:274) checks the unsigned tag and resolved volume/file identity. Receipt-mode validation precedes the summary ([line 595](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:595)).

- **GET signature/buffers:** [test lines 92–100](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:92) use appropriate handle/pointer types, null input/zero bytes, a 16,384-byte output, and a 32-bit returned count for `0x900A8`. Signed `int` counts preserve the native DWORD width and accommodate these sizes. Explicit `[Out]` would clarify the blittable output array; no demonstrated marshaling defect exists. The oracle should additionally require `$n -ge 8`.

- **Opening is correct:** oracle access **0**, share **7**, disposition **3**; producer metadata access **0**, creation access **GENERIC_WRITE**, share **1**. Both raw opens combine `FILE_FLAG_OPEN_REPARSE_POINT` **0x00200000** and `FILE_FLAG_BACKUP_SEMANTICS` **0x02000000**. Producer identity validation deliberately follows the junction.

**Minimal correction:** replace the expected literal at test line 100 with `[uint32]2684354563`.

**Uncertainty:** the retained temporary directory was empty; no actual returned bytes/count were available. The supplied failure context and code establish the comparison defect, but do not independently expose the filesystem’s numeric tag.

One-shot numeric oracle, **not executed**, requiring no filesystem access:

```powershell
powershell.exe -NoProfile -NonInteractive -Command '$v=[BitConverter]::ToUInt32([byte[]](3,0,0,160),0); "actual=$v literal=$(0xA0000003) oldMismatch=$($v -ne 0xA0000003) correctedMatch=$($v -eq [uint32]2684354563)"'
```

Expected: `actual=2684354563 literal=-1610612733 oldMismatch=True correctedMatch=True`

No files changed; no tests or link probes executed.