/* RISC-V freestanding runtime bridge.
 *
 * This file is compiled as a boot object by native-build for the RV64 entry.
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;
typedef unsigned int spl_u32;
typedef unsigned char spl_u8;

#define RT_VALUE_TAG_MASK 0x7ULL
#define RT_VALUE_TAG_INT 0x0ULL
#define RT_VALUE_TAG_HEAP 0x1ULL
#define RT_VALUE_TAG_SPECIAL 0x3ULL
#define RT_VALUE_SPECIAL_NIL 0x0ULL
#define RT_VALUE_SPECIAL_TRUE 0x1ULL
#define RT_VALUE_SPECIAL_FALSE 0x2ULL
#define RT_HEAP_STRING 0x01U
#define RT_HEAP_ARRAY 0x02U
#define RT_HEAP_TUPLE 0x04U
#define RT_HEAP_ENUM 0x07U

typedef struct RtHeapHeader {
    spl_u8 object_type;
    spl_u8 gc_flags;
    unsigned short reserved;
    spl_u32 size;
} RtHeapHeader;

typedef struct RtString {
    RtHeapHeader header;
    spl_u64 len;
    spl_u64 hash;
    char data[];
} RtString;

typedef struct RtArray {
    RtHeapHeader header;
    spl_u64 len;
    spl_u64 capacity;
    spl_i64 *data;
} RtArray;

typedef struct RtTuple {
    RtHeapHeader header;
    spl_u64 len;
    spl_i64 data[];
} RtTuple;

typedef struct RtEnum {
    RtHeapHeader header;
    spl_u32 enum_id;
    spl_u32 discriminant;
    spl_i64 payload;
} RtEnum;

__asm__(
    ".section .text.entry,\"ax\",@progbits\n"
    ".globl _start\n"
    "_start:\n"
    "j spl_start\n"
);

extern spl_i64 kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(spl_i64 size) __attribute__((weak));

static spl_u64 g_freestanding_heap_next = 0x87000000ULL;
static spl_u64 g_freestanding_heap_limit = 0x88000000ULL;

static spl_u64 rt_align8(spl_u64 value) {
    return (value + 7ULL) & ~7ULL;
}

void *rt_alloc(spl_i64 size) {
    spl_u64 next;
    spl_u64 bytes;
    if (size <= 0) {
        return (void *)0;
    }
    if (kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc) {
        return (void *)(spl_u64)kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(size);
    }
    bytes = rt_align8((spl_u64)size);
    next = rt_align8(g_freestanding_heap_next);
    if (next + bytes > g_freestanding_heap_limit) {
        return (void *)0;
    }
    g_freestanding_heap_next = next + bytes;
    return (void *)next;
}

void rt_free(void *ptr) {
    (void)ptr;
}

void *rt_memcpy(void *dst, const void *src, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = s[i];
    }
    return dst;
}

void *rt_memset(void *dst, signed char val, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = (unsigned char)val;
    }
    return dst;
}

static spl_i64 rt_special(spl_u64 payload) {
    return (spl_i64)((payload << 3) | RT_VALUE_TAG_SPECIAL);
}

static spl_i64 rt_nil(void) {
    return rt_special(RT_VALUE_SPECIAL_NIL);
}

static spl_i64 rt_heap(void *ptr) {
    if (!ptr) {
        return rt_nil();
    }
    return (spl_i64)(((spl_u64)ptr) | RT_VALUE_TAG_HEAP);
}

static RtHeapHeader *rt_as_heap(spl_i64 value, spl_u8 kind) {
    spl_u64 raw = (spl_u64)value;
    RtHeapHeader *header;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) {
        return (RtHeapHeader *)0;
    }
    header = (RtHeapHeader *)(raw & ~RT_VALUE_TAG_MASK);
    if (!header || header->object_type != kind) {
        return (RtHeapHeader *)0;
    }
    return header;
}

static RtString *rt_as_string(spl_i64 value) {
    return (RtString *)rt_as_heap(value, RT_HEAP_STRING);
}

static RtArray *rt_as_array(spl_i64 value) {
    return (RtArray *)rt_as_heap(value, RT_HEAP_ARRAY);
}

static RtTuple *rt_as_tuple(spl_i64 value) {
    return (RtTuple *)rt_as_heap(value, RT_HEAP_TUPLE);
}

static RtEnum *rt_as_enum(spl_i64 value) {
    return (RtEnum *)rt_as_heap(value, RT_HEAP_ENUM);
}

static spl_i64 rt_index_arg(spl_i64 value) {
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
        return value >> 3;
    }
    return value;
}

static void rt_write_decimal(char *buf, spl_u64 *len, spl_u64 value) {
    char tmp[20];
    spl_u64 count = 0;
    if (value == 0) {
        buf[0] = '0';
        *len = 1;
        return;
    }
    while (value > 0) {
        tmp[count] = (char)('0' + (value % 10));
        value = value / 10;
        count = count + 1;
    }
    *len = count;
    for (spl_u64 i = 0; i < count; i = i + 1) {
        buf[i] = tmp[count - 1 - i];
    }
}

spl_i64 rt_string_new(spl_i64 bytes_value, spl_i64 len_value) {
    const spl_u8 *bytes = (const spl_u8 *)(spl_u64)bytes_value;
    spl_u64 len = len_value < 0 ? 0 : (spl_u64)len_value;
    RtString *out = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + len + 1));
    if (!out) {
        return rt_nil();
    }
    out->header.object_type = RT_HEAP_STRING;
    out->header.gc_flags = 0;
    out->header.reserved = 0;
    out->header.size = (spl_u32)(sizeof(RtString) + len);
    out->len = len;
    out->hash = 0;
    for (spl_u64 i = 0; i < len; i = i + 1) {
        out->data[i] = bytes ? (char)bytes[i] : 0;
    }
    out->data[len] = 0;
    return rt_heap(out);
}

spl_i64 rt_raw_u64_to_string(spl_i64 raw) {
    char buf[20];
    spl_u64 len = 0;
    rt_write_decimal(buf, &len, (spl_u64)raw);
    return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)len);
}

spl_i64 rt_to_string(spl_i64 value) {
    char buf[21];
    spl_u64 len = 0;
    spl_i64 signed_value;
    if (rt_as_string(value)) {
        return value;
    }
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
        signed_value = value >> 3;
        if (signed_value < 0) {
            buf[0] = '-';
            rt_write_decimal(buf + 1, &len, (spl_u64)(-signed_value));
            return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)(len + 1));
        }
        rt_write_decimal(buf, &len, (spl_u64)signed_value);
        return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)len);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) {
        return rt_string_new((spl_i64)(spl_u64)"true", 4);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) {
        return rt_string_new((spl_i64)(spl_u64)"false", 5);
    }
    if (value == rt_nil()) {
        return rt_string_new((spl_i64)(spl_u64)"nil", 3);
    }
    return rt_string_new((spl_i64)(spl_u64)"<value>", 7);
}

spl_i64 rt_value_to_string(spl_i64 value) {
    return rt_to_string(value);
}

spl_i64 rt_string_concat(spl_i64 left, spl_i64 right) {
    RtString *a;
    RtString *b;
    RtString *out;
    spl_i64 left_text = rt_to_string(left);
    spl_i64 right_text = rt_to_string(right);
    a = rt_as_string(left_text);
    b = rt_as_string(right_text);
    if (!a || !b) {
        return rt_nil();
    }
    out = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + a->len + b->len + 1));
    if (!out) {
        return rt_nil();
    }
    out->header.object_type = RT_HEAP_STRING;
    out->header.gc_flags = 0;
    out->header.reserved = 0;
    out->header.size = (spl_u32)(sizeof(RtString) + a->len + b->len);
    out->len = a->len + b->len;
    out->hash = 0;
    for (spl_u64 i = 0; i < a->len; i = i + 1) {
        out->data[i] = a->data[i];
    }
    for (spl_u64 i = 0; i < b->len; i = i + 1) {
        out->data[a->len + i] = b->data[i];
    }
    out->data[out->len] = 0;
    return rt_heap(out);
}

spl_i64 rt_len(spl_i64 value) {
    RtString *s = rt_as_string(value);
    RtArray *a;
    RtTuple *t;
    if (s) {
        return (spl_i64)s->len;
    }
    a = rt_as_array(value);
    if (a) {
        return (spl_i64)a->len;
    }
    t = rt_as_tuple(value);
    if (t) {
        return (spl_i64)t->len;
    }
    return 0;
}

spl_i64 rt_array_new(spl_i64 capacity_value) {
    spl_u64 capacity = capacity_value <= 4 ? 4 : (spl_u64)capacity_value;
    RtArray *array = (RtArray *)rt_alloc((spl_i64)sizeof(RtArray));
    if (!array) {
        return rt_nil();
    }
    array->data = (spl_i64 *)rt_alloc((spl_i64)(capacity * sizeof(spl_i64)));
    if (!array->data) {
        return rt_nil();
    }
    array->header.object_type = RT_HEAP_ARRAY;
    array->header.gc_flags = 0;
    array->header.reserved = 0;
    array->header.size = (spl_u32)sizeof(RtArray);
    array->len = 0;
    array->capacity = capacity;
    for (spl_u64 i = 0; i < capacity; i = i + 1) {
        array->data[i] = rt_nil();
    }
    return rt_heap(array);
}

spl_i64 rt_array_len(spl_i64 array_value) {
    RtArray *array = rt_as_array(array_value);
    return array ? (spl_i64)array->len : -1;
}

spl_i64 rt_array_push(spl_i64 array_value, spl_i64 value) {
    RtArray *array = rt_as_array(array_value);
    spl_i64 *new_data;
    spl_u64 new_capacity;
    if (!array) {
        return 0;
    }
    if (array->len >= array->capacity) {
        new_capacity = array->capacity < 4 ? 4 : array->capacity * 2;
        new_data = (spl_i64 *)rt_alloc((spl_i64)(new_capacity * sizeof(spl_i64)));
        if (!new_data) {
            return 0;
        }
        for (spl_u64 i = 0; i < array->len; i = i + 1) {
            new_data[i] = array->data[i];
        }
        for (spl_u64 i = array->len; i < new_capacity; i = i + 1) {
            new_data[i] = rt_nil();
        }
        array->data = new_data;
        array->capacity = new_capacity;
    }
    array->data[array->len] = value;
    array->len = array->len + 1;
    return 1;
}

spl_i64 rt_index_get(spl_i64 collection, spl_i64 index_value) {
    RtArray *array = rt_as_array(collection);
    RtTuple *tuple;
    RtString *string;
    spl_i64 index = rt_index_arg(index_value);
    if (array) {
        if (index < 0) {
            index = (spl_i64)array->len + index;
        }
        if (index < 0 || (spl_u64)index >= array->len) {
            return rt_nil();
        }
        return array->data[index];
    }
    tuple = rt_as_tuple(collection);
    if (tuple) {
        if (index < 0) {
            index = (spl_i64)tuple->len + index;
        }
        if (index < 0 || (spl_u64)index >= tuple->len) {
            return rt_nil();
        }
        return tuple->data[index];
    }
    string = rt_as_string(collection);
    if (string) {
        if (index < 0) {
            index = (spl_i64)string->len + index;
        }
        if (index < 0 || (spl_u64)index >= string->len) {
            return rt_nil();
        }
        return rt_string_new((spl_i64)(spl_u64)&string->data[index], 1);
    }
    return rt_nil();
}

spl_i64 rt_index_set(spl_i64 collection, spl_i64 index_value, spl_i64 value) {
    RtArray *array = rt_as_array(collection);
    spl_i64 index = rt_index_arg(index_value);
    if (!array) {
        return 0;
    }
    if (index < 0) {
        index = (spl_i64)array->len + index;
    }
    if (index < 0 || (spl_u64)index >= array->len) {
        return 0;
    }
    array->data[index] = value;
    return 1;
}

spl_i64 rt_slice(spl_i64 value, spl_i64 start_value, spl_i64 end_value, spl_i64 step_value) {
    RtString *string = rt_as_string(value);
    spl_i64 start = rt_index_arg(start_value);
    spl_i64 end = rt_index_arg(end_value);
    spl_i64 step = rt_index_arg(step_value);
    if (!string) {
        return rt_nil();
    }
    if (step == 0) {
        step = 1;
    }
    if (start < 0) {
        start = (spl_i64)string->len + start;
    }
    if (end < 0) {
        end = (spl_i64)string->len + end;
    }
    if (start < 0) {
        start = 0;
    }
    if (end < start) {
        end = start;
    }
    if ((spl_u64)end > string->len) {
        end = (spl_i64)string->len;
    }
    if (step != 1) {
        return rt_string_new((spl_i64)(spl_u64)"", 0);
    }
    return rt_string_new((spl_i64)(spl_u64)&string->data[start], end - start);
}

spl_i64 rt_array_repeat(spl_i64 value, spl_i64 count_value) {
    spl_i64 count = rt_index_arg(count_value);
    spl_i64 array;
    if (count <= 0) {
        return rt_array_new(0);
    }
    array = rt_array_new(count);
    for (spl_i64 i = 0; i < count; i = i + 1) {
        rt_array_push(array, value);
    }
    return array;
}

spl_i64 rt_tuple_new(spl_i64 len_value) {
    spl_u64 len = len_value < 0 ? 0 : (spl_u64)len_value;
    RtTuple *tuple = (RtTuple *)rt_alloc((spl_i64)(sizeof(RtTuple) + len * sizeof(spl_i64)));
    if (!tuple) {
        return rt_nil();
    }
    tuple->header.object_type = RT_HEAP_TUPLE;
    tuple->header.gc_flags = 0;
    tuple->header.reserved = 0;
    tuple->header.size = (spl_u32)(sizeof(RtTuple) + len * sizeof(spl_i64));
    tuple->len = len;
    for (spl_u64 i = 0; i < len; i = i + 1) {
        tuple->data[i] = rt_nil();
    }
    return rt_heap(tuple);
}

spl_i64 rt_tuple_get(spl_i64 tuple_value, spl_i64 index_value) {
    RtTuple *tuple = rt_as_tuple(tuple_value);
    spl_i64 index = rt_index_arg(index_value);
    if (!tuple || index < 0 || (spl_u64)index >= tuple->len) {
        return rt_nil();
    }
    return tuple->data[index];
}

spl_i64 rt_tuple_set(spl_i64 tuple_value, spl_i64 index_value, spl_i64 value) {
    RtTuple *tuple = rt_as_tuple(tuple_value);
    spl_i64 index = rt_index_arg(index_value);
    if (!tuple || index < 0 || (spl_u64)index >= tuple->len) {
        return 0;
    }
    tuple->data[index] = value;
    return 1;
}

spl_i64 rt_enum_new(spl_u32 enum_id, spl_u32 discriminant, spl_i64 payload) {
    RtEnum *value = (RtEnum *)rt_alloc((spl_i64)sizeof(RtEnum));
    if (!value) {
        return rt_nil();
    }
    value->header.object_type = RT_HEAP_ENUM;
    value->header.gc_flags = 0;
    value->header.reserved = 0;
    value->header.size = (spl_u32)sizeof(RtEnum);
    value->enum_id = enum_id;
    value->discriminant = discriminant;
    value->payload = payload;
    return rt_heap(value);
}

spl_i64 rt_enum_payload(spl_i64 value) {
    RtEnum *enum_value = rt_as_enum(value);
    return enum_value ? enum_value->payload : rt_nil();
}

spl_i64 rt_enum_check_discriminant(spl_i64 value, spl_i64 expected) {
    RtEnum *enum_value = rt_as_enum(value);
    return enum_value && enum_value->discriminant == (spl_u32)expected ? 1 : 0;
}

spl_i64 common__config_env__ConfigEnv_dot_len(spl_i64 value) {
    (void)value;
    return 0;
}

spl_i64 rt_native_eq(spl_i64 lhs, spl_i64 rhs) {
    RtString *a = rt_as_string(lhs);
    RtString *b = rt_as_string(rhs);
    if (a || b) {
        if (!a || !b || a->len != b->len) {
            return 0;
        }
        for (spl_u64 i = 0; i < a->len; i = i + 1) {
            if (a->data[i] != b->data[i]) {
                return 0;
            }
        }
        return 1;
    }
    return lhs == rhs ? 1 : 0;
}

spl_i64 rt_native_neq(spl_i64 lhs, spl_i64 rhs) {
    return rt_native_eq(lhs, rhs) ? 0 : 1;
}

spl_i64 rt_mmio_read_u8(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned char *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u16(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned short *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u32(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned int *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u64(spl_i64 addr) {
    return (spl_i64)(*(volatile spl_u64 *)(spl_u64)addr);
}

void rt_mmio_write_u8(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned char *)(spl_u64)addr = (unsigned char)value;
}

void rt_mmio_write_u16(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned short *)(spl_u64)addr = (unsigned short)value;
}

void rt_mmio_write_u32(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned int *)(spl_u64)addr = (unsigned int)value;
}

void rt_mmio_write_u64(spl_i64 addr, spl_i64 value) {
    *(volatile spl_u64 *)(spl_u64)addr = (spl_u64)value;
}

static void uart_put_byte(spl_u8 byte) {
    *(volatile spl_u8 *)0x10000000ULL = byte;
}

void rt_riscv_uart_put(spl_u64 byte) {
    uart_put_byte((spl_u8)byte);
}

static void uart_write_bytes(const char *data, spl_u64 len) {
    if (!data) {
        return;
    }
    for (spl_u64 i = 0; i < len; i = i + 1) {
        uart_put_byte((spl_u8)data[i]);
    }
}

void log_raw_println(spl_i64 msg) {
    RtString *text = rt_as_string(msg);
    spl_i64 rendered;
    if (!text) {
        rendered = rt_to_string(msg);
        text = rt_as_string(rendered);
    }
    if (text) {
        uart_write_bytes(text->data, text->len);
    }
    uart_put_byte(13);
    uart_put_byte(10);
}

spl_i64 vmm_map_page(spl_i64 virt, spl_i64 phys, spl_i64 flags) {
    (void)flags;
    return virt == phys ? 1 : 0;
}

typedef struct RtPciDevice {
    spl_i64 bus;
    spl_i64 device;
    spl_i64 function;
    spl_i64 class_code;
    spl_i64 subclass;
    spl_i64 vendor;
    spl_i64 device_id;
    spl_i64 bar0;
    spl_i64 irq;
} RtPciDevice;

#define RT_PCI_ECAM_BASE 0x30000000ULL
#define RT_PCI_MAX_DEVICES 8

static RtPciDevice g_rt_pci_devices[RT_PCI_MAX_DEVICES];
static spl_i64 g_rt_pci_count = -1;
static spl_i64 g_rt_net_ready = 0;

static spl_u32 rt_pci_read_config32(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + (reg & ~3ULL);
    return *(volatile spl_u32 *)addr;
}

static void rt_pci_scan_qemu_virt(void) {
    g_rt_pci_count = 0;
    for (spl_u64 dev = 0; dev < 32 && g_rt_pci_count < RT_PCI_MAX_DEVICES; dev = dev + 1) {
        spl_u32 id = rt_pci_read_config32(0, dev, 0, 0);
        spl_u32 class_reg;
        spl_u32 bar0;
        RtPciDevice *out;
        if ((id & 0xffffU) == 0xffffU) {
            continue;
        }
        class_reg = rt_pci_read_config32(0, dev, 0, 8);
        bar0 = rt_pci_read_config32(0, dev, 0, 0x10);
        out = &g_rt_pci_devices[g_rt_pci_count];
        out->bus = 0;
        out->device = (spl_i64)dev;
        out->function = 0;
        out->class_code = (spl_i64)((class_reg >> 24) & 0xffU);
        out->subclass = (spl_i64)((class_reg >> 16) & 0xffU);
        out->vendor = (spl_i64)(id & 0xffffU);
        out->device_id = (spl_i64)((id >> 16) & 0xffffU);
        out->bar0 = (spl_i64)(bar0 & ~0xfU);
        out->irq = 0;
        g_rt_pci_count = g_rt_pci_count + 1;
    }
}

spl_i64 rt_pci_device_count(void) {
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    return g_rt_pci_count;
}

spl_i64 rt_pci_get_field(spl_i64 index, spl_i64 field) {
    RtPciDevice *dev;
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    if (index < 0 || index >= g_rt_pci_count) {
        return -1;
    }
    dev = &g_rt_pci_devices[index];
    if (field == 0) return dev->bus;
    if (field == 1) return dev->device;
    if (field == 2) return dev->function;
    if (field == 3) return dev->class_code;
    if (field == 4) return dev->subclass;
    if (field == 5) return dev->vendor;
    if (field == 6) return dev->device_id;
    if (field == 7) return dev->bar0;
    if (field == 8) return dev->irq;
    return -1;
}

spl_i64 rt_net_init(void) {
    spl_i64 count = rt_pci_device_count();
    for (spl_i64 i = 0; i < count; i = i + 1) {
        spl_i64 cls = rt_pci_get_field(i, 3);
        spl_i64 sub = rt_pci_get_field(i, 4);
        spl_i64 vendor = rt_pci_get_field(i, 5);
        if (cls == 2 && sub == 0 && vendor == 0x1af4) {
            g_rt_net_ready = 1;
            return 0;
        }
    }
    g_rt_net_ready = 0;
    return -1;
}

spl_i64 rt_net_tx_test(void) {
    return g_rt_net_ready ? 0 : -1;
}

spl_i64 rt_net_stats(void) {
    return g_rt_net_ready ? 0 : -1;
}

__attribute__((weak)) spl_i64 rt_io_tcp_bind(spl_i64 addr) {
    (void)addr;
    return -1;
}

__attribute__((weak)) spl_i64 rt_io_tcp_accept_timeout(spl_i64 fd, spl_i64 ms) {
    (void)fd;
    (void)ms;
    return -1;
}

__attribute__((weak)) spl_i64 rt_io_tcp_write_text(spl_i64 fd, spl_i64 data) {
    RtString *text = rt_as_string(data);
    (void)fd;
    return text ? (spl_i64)text->len : -1;
}

__attribute__((weak)) spl_i64 rt_io_tcp_close(spl_i64 fd) {
    (void)fd;
    return 1;
}

spl_i64 rt_display_init(void) {
    return -1;
}

spl_i64 rt_display_flush_test(void) {
    return -1;
}

spl_i64 rt_display_width(void) {
    return 0;
}

spl_i64 rt_display_height(void) {
    return 0;
}
