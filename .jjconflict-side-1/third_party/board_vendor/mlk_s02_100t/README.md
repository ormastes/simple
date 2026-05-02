# MLK-S02-100T Vendor Bundle Staging

Place manually acquired MiLianKe `MLK-S02-35T-100T` vendor resources here.

Expected contents from the vendor bundle:
- XDC constraint files
- Vivado project files (`.xpr`, `.srcs`, `.tcl`)
- board-level wrapper examples
- LED/UART or other reference demos

Do not commit opaque large archives blindly.

Preferred workflow:
1. unpack the vendor archive here
2. identify the authoritative XDC and top-level example
3. copy only the needed facts into repo-native support files
4. document provenance in `doc/09_report/`
