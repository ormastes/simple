#include <stdint.h>

static int64_t mode;

void rt_hda_pci_probe_set_mode(int64_t value) {
    mode = value;
}

int64_t rt_pci_device_count(void) {
    if (mode == 0) return 0;
    if (mode == 1) return 1;
    if (mode == 2) return 3;
    if (mode == 3) return 2;
    return 257;
}

static int is_hda(int64_t index) {
    if (mode == 1) return index == 0;
    if (mode == 2) return index == 1;
    if (mode == 3) return index == 0 || index == 1;
    return 0;
}

int64_t rt_pci_get_field(int64_t index, int64_t field) {
    if (!is_hda(index)) {
        if (field == 3) return 3;
        return 0;
    }
    switch (field) {
        case 0: return 0;
        case 1: return 27;
        case 2: return 0;
        case 3: return 4;
        case 4: return 3;
        case 5: return 0x8086;
        case 6: return 0x2668;
        case 7:
            if (mode == 3 && index == 0) return 0;
            return 11;
        default: return 0;
    }
}

int64_t rt_pci_read_bar0(int64_t index) {
    if (!is_hda(index) || mode == 1 ||
        (mode == 3 && index == 0)) return 0;
    return INT64_C(0xfebf0008);
}

int64_t rt_pci_enable_memory_bus_master(int64_t index) {
    return is_hda(index) && rt_pci_read_bar0(index) != 0 ? 1 : 0;
}
