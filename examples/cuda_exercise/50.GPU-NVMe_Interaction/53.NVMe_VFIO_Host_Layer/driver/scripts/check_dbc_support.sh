#!/bin/bash
# Check Doorbell Buffer Config (DBC) support for all NVMe devices

echo "=== NVMe Doorbell Buffer Config (DBC) Support Check ==="
echo ""

for dev in /dev/nvme[0-9]; do
    if [ ! -e "$dev" ]; then
        continue
    fi

    echo "Device: $dev"
    echo "----------------------------------------"

    # Get model name
    model=$(nvme id-ctrl "$dev" 2>/dev/null | grep "^mn " | cut -d: -f2- | xargs)
    echo "Model: $model"

    # Get OACS value
    oacs=$(nvme id-ctrl "$dev" 2>/dev/null | grep "^oacs " | cut -d: -f2 | xargs)
    echo "OACS: $oacs"

    # Convert hex to decimal and check bit 8
    if [ -n "$oacs" ]; then
        # Remove 0x prefix if present
        oacs_hex="${oacs#0x}"
        oacs_dec=$((16#$oacs_hex))

        # Check bit 8 (value 256 = 0x100)
        if [ $((oacs_dec & 0x100)) -ne 0 ]; then
            echo "DBC Support: ✓ YES (bit 8 is SET)"
        else
            echo "DBC Support: ✗ NO (bit 8 is NOT set)"
        fi
    else
        echo "DBC Support: Unable to read OACS"
    fi

    echo ""
done

echo "=== Summary ==="
echo "Bit 8 in OACS (Optional Admin Command Support) indicates DBC support"
echo "Bit 8 = 1 (0x100) → Controller supports Doorbell Buffer Config command (0x7C)"
echo "Bit 8 = 0 → Controller does NOT support hardware DBC"
