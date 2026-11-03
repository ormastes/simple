#!/usr/bin/env python3
"""Execute the production ARM64 TX publisher against a split-ring device model.

This is a host logic regression, not NIC, EL0, or firmware admission. Only the
cache-maintenance/device-completion boundary is substituted. The transport
structures, queue constants, zero helper, and send function come from source.
"""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def function(source, signature):
    start = source.index(signature)
    body = source.index("{", start)
    depth = 1
    end = body + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]


def fixture(source):
    declarations = source[source.index("#define ARM64_VIRTIO_NET_DEVICE_ID"):
                          source.index("static void arm64_net_zero")]
    zero = function(source, "static void arm64_net_zero(")
    send = function(source, "RuntimeValue rt_arm64_virtio_net_send(")
    return r'''
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
typedef int64_t RuntimeValue;
''' + declarations + zero + r'''
static uint32_t mmio[128];
static uint16_t device_next;
static unsigned consumed;
static void arm64_clean_dcache_range(uint64_t address, uint64_t length) {
    (void)address; (void)length;
}
static void arm64_invalidate_dcache_range(uint64_t address, uint64_t length) {
    (void)address; (void)length;
    /* Device consumes the next available RING position, never a CPU-selected
     * descriptor slot. Completion identity is copied from that ring entry. */
    if (device_next != g_arm64_net_tx_avail.idx) {
        uint16_t desc = g_arm64_net_tx_avail.ring[device_next % ARM64_NET_QUEUE_SIZE];
        uint16_t used = g_arm64_net_tx_used.idx % ARM64_NET_QUEUE_SIZE;
        g_arm64_net_tx_used.ring[used].id = desc;
        g_arm64_net_tx_used.ring[used].len = 0;
        g_arm64_net_tx_used.idx++;
        device_next++;
        consumed++;
    }
}
''' + send + r'''
static int run_case(uint16_t producer, uint16_t descriptor) {
    memset(mmio, 0, sizeof(mmio));
    memset(&g_arm64_net_tx_avail, 0, sizeof(g_arm64_net_tx_avail));
    memset(&g_arm64_net_tx_used, 0, sizeof(g_arm64_net_tx_used));
    memset(g_arm64_net_tx_desc, 0, sizeof(g_arm64_net_tx_desc));
    /* Prior device-owned descriptors may survive timed-out sends. Give the
     * CPU exactly one reusable slot; stale ring contents identify another. */
    memset(g_arm64_net_tx_posted, 1, sizeof(g_arm64_net_tx_posted));
    g_arm64_net_tx_posted[descriptor] = 0;
    for (unsigned i = 0; i < ARM64_NET_QUEUE_SIZE; ++i)
        g_arm64_net_tx_avail.ring[i] = (descriptor + 1) % ARM64_NET_QUEUE_SIZE;
    g_arm64_net_tx_avail.idx = producer;
    g_arm64_net_tx_used.idx = producer;
    g_arm64_net_tx_last_used = producer;
    g_arm64_net_tx_completions = 0;
    g_arm64_net_base = (uint64_t)(uintptr_t)mmio;
    g_arm64_net_ready = 1;
    device_next = producer;
    consumed = 0;
    uint8_t packet[] = {0x52, 0x54, 0x00, 0xab};
    int64_t result = rt_arm64_virtio_net_send(
        (uint64_t)(uintptr_t)packet, sizeof(packet));
    if (result != sizeof(packet) || consumed != 1 ||
        g_arm64_net_tx_completions != 1 || g_arm64_net_tx_posted[descriptor] ||
        g_arm64_net_tx_avail.idx != (uint16_t)(producer + 1) ||
        g_arm64_net_tx_avail.ring[producer % ARM64_NET_QUEUE_SIZE] != descriptor ||
        memcmp(g_arm64_net_tx_buf[descriptor] + ARM64_NET_HEADER_SIZE,
               packet, sizeof(packet)) != 0) {
        fprintf(stderr, "TX ring mismatch producer=%u descriptor=%u result=%lld\n",
                producer, descriptor, (long long)result);
        return 1;
    }
    for (unsigned i = 0; i < ARM64_NET_QUEUE_SIZE; ++i)
        if (i != descriptor && g_arm64_net_tx_posted[i] != 1) return 2;
    return 0;
}
int main(void) {
    const uint16_t cursors[] = {0, 1, 5, 7, 8, 15, 65535};
    for (unsigned i = 0; i < sizeof(cursors) / sizeof(cursors[0]); ++i)
        for (uint16_t slot = 0; slot < ARM64_NET_QUEUE_SIZE; ++slot)
            if (run_case(cursors[i], slot)) return 1;
    puts("PASS ARM64 TX split-ring cursor: 56 publication/reuse/wrap cases");
    return 0;
}
'''


def run(cc, source, directory, name):
    code = directory / (name + ".c")
    binary = directory / name
    code.write_text(fixture(source))
    subprocess.run([cc, "-std=c11", "-O2", str(code), "-o", str(binary)], check=True)
    return subprocess.run([str(binary)], text=True, capture_output=True, timeout=10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parents[2] /
                        "examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
    parser.add_argument("--cc", default=os.environ.get("CC", "cc"))
    parser.add_argument("--negative-control", action="store_true")
    args = parser.parse_args()
    source = args.source.read_text()
    with tempfile.TemporaryDirectory(prefix="arm64-net-tx-ring-") as temporary:
        directory = Path(temporary)
        result = run(args.cc, source, directory, "production")
        print(result.stdout, end="")
        print(result.stderr, end="")
        if result.returncode:
            return result.returncode
        if args.negative_control:
            fixed = "g_arm64_net_tx_avail.ring[avail_slot] = slot;"
            assert source.count(fixed) == 1, "negative control requires the repaired publisher"
            mutant = source.replace(fixed, "g_arm64_net_tx_avail.ring[slot] = slot;")
            negative = run(args.cc, mutant, directory, "old-publisher")
            if negative.returncode != 1 or "TX ring mismatch" not in negative.stderr:
                raise RuntimeError("regression did not reject the old descriptor-index publisher")
            print("PASS negative control: old descriptor-index publisher rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
