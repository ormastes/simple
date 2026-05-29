# Vivado Device Family Installation Guide

Vivado 2025.2 installs without device support by default. Building for specific
FPGA parts (e.g., xck26, xczu5ev, xc7a100t) requires installing the
corresponding device family after the initial Vivado installation.

## Check Installed Devices

In the Vivado TCL console:

```tcl
llength [get_parts]                    # total count
get_parts xczu*                        # Zynq UltraScale+
get_parts xc7a*                        # Artix-7
get_parts xck*                         # Kria SOMs
```

If the result is empty or the target part is missing, install the device family.

## Required Families by Board

| Board | Device Family | Part |
|-------|--------------|------|
| Kria K26 (ML Carrier) | Zynq UltraScale+ MPSoC | xck26-sfvc784-2lv-c |
| MLK-S02-100T | Artix-7 | xc7a100t-2ffg484i |
| ZedBoard | Zynq-7000 | xc7z020-clg484-1 |

## Installation via Unified Installer (GUI)

Launch the installer:

```
/home/ormastes/Xilinx/2025.2/xsetup
```

Select **"Add Design Tools or Devices"** → check required device families →
Install.

## Installation via Command Line (Batch)

```
/home/ormastes/Xilinx/2025.2/xsetup --batch AddDesignTools
```

## Verification

```bash
source /home/ormastes/Xilinx/2025.2/Vivado/settings64.sh
vivado -mode batch -source /dev/stdin <<'EOF'
puts "Parts: [llength [get_parts]]"
puts "ZU+: [llength [get_parts xczu*]]"
puts "Kria: [llength [get_parts xck*]]"
puts "A7: [llength [get_parts xc7a*]]"
exit
EOF
```

Expected output shows non-zero counts for each installed family.

## Known Issue

Kria parts (xck26) may require the **"Kria KV260" board files** from the
Xilinx Board Store. These should be located at:

```
/home/ormastes/Xilinx/2025.2/data/xhub/boards/XilinxBoardStore/
```

If board files are missing, use the Vivado TCL console to install them:

```tcl
xhub::refresh_catalog [xhub::get_xstores]
xhub::install [xhub::get_xitems *kv260*]
```
