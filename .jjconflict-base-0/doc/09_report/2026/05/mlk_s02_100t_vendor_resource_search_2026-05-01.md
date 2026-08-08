# MLK-S02-100T Vendor Resource Search

**Date:** 2026-05-01
**Status:** Search complete, direct bundle download blocked by vendor access model
**Board:** MiLianKe `MLK-S02-100T`

## Result

The vendor resource bundle for this board appears to exist, but it is not openly downloadable from the public web without the vendor site's purchase or login flow.

What is confirmed:
- `MLK-S02-35T-100T` appears on the MiLianKe resource download catalog.
- The resource entry is listed as a paid download (`¥100`) on `uisrc.com`.
- The public hardware manual is accessible and confirms the board family and core hardware facts.

What is not available from this session:
- direct public XDC download URL
- direct public Vivado project archive URL
- direct public example bundle URL

## Sources

- Hardware manual:
  - https://www.cnblogs.com/milianke/p/17683342.html
- Vendor download catalog:
  - https://www.uisrc.com/download.html
- Vendor download list page:
  - https://www.uisrc.com/download_list-0-0-0-1-1.html
- Product/community page:
  - https://www.uisrc.com/forum.php?aid=24119&from=album&mobile=2&mod=viewthread&page=1&tid=6264

## Publicly Observable Catalog Evidence

The public search index shows:
- `MLK-S02-35T-100T`
- vendor: `米联客-课程团队`
- price: `¥100`

This is enough to conclude the vendor bundle likely contains the relevant board support files, but the bundle is not openly fetchable here.

## Recommended Manual Acquisition Path

1. Open `https://www.uisrc.com/download.html`
2. Search for `MLK-S02-35T-100T`
3. Purchase or log in as required by MiLianKe
4. Download the board bundle
5. Extract and look for:
   - `.xdc`
   - `.xpr`
   - `*.tcl`
   - top-level wrapper files
   - LED / UART / DDR example projects

## Repo Integration Target

When the vendor bundle is available locally, integrate it into this repo by harvesting only the authoritative facts needed for support:

- verified pin assignments into `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc`
- verified wrapper wiring into `examples/09_embedded/fpga_riscv/rtl/`
- verified build/program steps into `build_mlk_s02_100t.tcl` and `program_mlk_s02_100t.tcl`

## Current Repo State

This repo now contains:
- board facts file
- logical I/O contract
- XDC scaffold
- wrapper scaffold
- build/program scaffolds

The missing piece is the authoritative vendor bundle or another trustworthy pin map source.
