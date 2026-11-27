# p3-manual-link-stage3.shs omits -lwinhttp (2026-11-05, P2)

Symptom (W1 probe, C:/dev/wt/w1_probe/out_rp3/nb.log.err, stage3 s3_fable44):
hosted Windows link with the full runtime fails with `ld.lld: undefined symbol:
__declspec(dllimport) WinHttpOpen` (+ WinHttpCrackUrl/Connect/OpenRequest/
SendRequest/ReceiveResponse/QueryHeaders/ReadData/SetOption/SetTimeouts/CloseHandle).

Root cause: commit e65e0e6b891 (WinHTTP provider for the Windows native HTTP
client) added `winhttp` to the compiler's mingw link lists
(`shared_linking.spl:147,426`, `native_all_support.spl:125/152`), but not to the
manual stage3 link line in `scripts/bootstrap/p3-manual-link-stage3.shs:168`.
s3_fable44.exe contains no "winhttp" string at all: it was linked from a tree
predating e65e0e6b891, so its in-process native-build link line lacks it too.
That binary-side half is closed by redeploying a stage3 built from current source.

Fix: add `-lwinhttp` to the manual link line (clang + lld, llvm-mingw import lib).
