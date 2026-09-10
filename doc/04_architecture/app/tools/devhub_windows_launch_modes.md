<!-- codex-design -->
# DevHub Windows mode boundary

`bin/devhub.cmd` transports arguments through `sh.exe` to `bin/devhub`.
The shared wrapper owns selection before any artifact probe. Ordinary uses
the existing native host/provenance boundary. Loading terminates with exit 78.
There is no transition between modes after failure and no loader execution.

The interrupted design proposed `loader --runtime runtime run entry`; no
in-tree executable was found implementing this contract. Moreover, current
provenance admission directly runs `--version`, and DevHub probes `--help`.
That path cannot recover an executable blocked by antivirus. A future loading
implementation needs a real trusted runtime/artifact format and behavioral
verification before replacing the unsupported branch. Hash receipts identify
build artifacts; they are not antivirus classification or publisher signatures.
