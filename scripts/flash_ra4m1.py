#!/usr/bin/env python3
"""Flash RA4M1 via OpenOCD TCL interface + FACI register writes.

Usage:
  1. Start OpenOCD:  openocd -f scripts/openocd_ra4m1.cfg
  2. Run this:       python3 scripts/flash_ra4m1.py build/os/simpleos_ra4m1.bin

Drives the Renesas FACI (Flash Application Command Interface) to erase
and program code flash on the RA4M1 (R7FA4M1AB).
"""
import socket, struct, sys, time

FACI_CMD   = 0x407E0000
FSTATR     = 0x407FE080
FENTRYR    = 0x407FE084
FSADDR     = 0x407FE030
FSUINITR   = 0x407FE024

BLOCK_SIZE = 2048
PROG_UNIT  = 64     # RA4M1 CF programming unit
PROG_WORDS = 32     # half-words per programming unit (64/2)

def ocd(sock, cmd):
    sock.send((cmd + '\x1a').encode())
    buf = b''
    while not buf.endswith(b'\x1a'):
        buf += sock.recv(4096)
    return buf[:-1].decode().strip()

def read32(sock, addr):
    r = ocd(sock, f'ocd_mdw 0x{addr:08x}')
    return int(r.split(':')[-1].strip().split()[0], 16)

def wait_frdy(sock, timeout=2.0):
    t0 = time.time()
    while time.time() - t0 < timeout:
        st = read32(sock, FSTATR)
        if st & 0x8000:
            return st
        time.sleep(0.005)
    raise TimeoutError(f'FACI timeout, FSTATR=0x{read32(sock, FSTATR):08x}')

def main():
    if len(sys.argv) < 2:
        print(f'Usage: {sys.argv[0]} <binary.bin>')
        sys.exit(1)

    with open(sys.argv[1], 'rb') as f:
        data = f.read()

    pad = (PROG_UNIT - len(data) % PROG_UNIT) % PROG_UNIT
    data += b'\xff' * pad

    num_blocks = (len(data) + BLOCK_SIZE - 1) // BLOCK_SIZE
    num_units = len(data) // PROG_UNIT

    print(f'Binary: {len(data)} bytes, {num_blocks} blocks, {num_units} program units')

    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect(('localhost', 6666))
    sock.settimeout(5)

    print('Halting CPU...')
    ocd(sock, 'halt')
    time.sleep(0.1)

    print('Entering P/E mode...')
    ocd(sock, f'mwh 0x{FENTRYR:08x} 0xAA01')
    time.sleep(0.01)
    fentr = read32(sock, FENTRYR)
    if not (fentr & 0x0001):
        print(f'WARNING: FENTRYR=0x{fentr:04x}, P/E mode may not be active')

    print(f'Erasing {num_blocks} blocks...')
    for i in range(num_blocks):
        addr = i * BLOCK_SIZE
        ocd(sock, f'mww 0x{FSADDR:08x} 0x{addr:08x}')
        ocd(sock, f'mwb 0x{FACI_CMD:08x} 0x20')
        ocd(sock, f'mwb 0x{FACI_CMD:08x} 0xD0')
        st = wait_frdy(sock, timeout=5.0)
        if st & 0x70:
            print(f'  Block {i} erase error: FSTATR=0x{st:08x}')
            ocd(sock, f'mwb 0x{FACI_CMD:08x} 0xB3')
            wait_frdy(sock)
            sys.exit(1)
        if (i+1) % 4 == 0 or i == num_blocks-1:
            print(f'  Erased {i+1}/{num_blocks}')

    print(f'Programming {num_units} units ({PROG_UNIT}B each)...')
    for u in range(num_units):
        offset = u * PROG_UNIT
        chunk = data[offset:offset+PROG_UNIT]

        ocd(sock, f'mww 0x{FSADDR:08x} 0x{offset:08x}')
        ocd(sock, f'mwb 0x{FACI_CMD:08x} 0xE8')
        ocd(sock, f'mwb 0x{FACI_CMD:08x} 0x{PROG_WORDS:02x}')

        for j in range(0, PROG_UNIT, 2):
            hw = struct.unpack('<H', chunk[j:j+2])[0]
            ocd(sock, f'mwh 0x{FACI_CMD:08x} 0x{hw:04x}')

        ocd(sock, f'mwb 0x{FACI_CMD:08x} 0xD0')
        st = wait_frdy(sock)
        if st & 0x70:
            print(f'  Program error at 0x{offset:08x}: FSTATR=0x{st:08x}')
            ocd(sock, f'mwb 0x{FACI_CMD:08x} 0xB3')
            wait_frdy(sock)
            sys.exit(1)

        if (u+1) % 50 == 0 or u == num_units-1:
            pct = 100*(u+1)//num_units
            print(f'  Programmed {(u+1)*PROG_UNIT}/{len(data)} bytes ({pct}%)')

    print('Exiting P/E mode...')
    ocd(sock, f'mwh 0x{FENTRYR:08x} 0xAA00')
    time.sleep(0.01)

    print('Verifying first 16 bytes...')
    for i in range(0, 16, 4):
        expected = struct.unpack('<I', data[i:i+4])[0]
        actual = read32(sock, i)
        status = 'OK' if actual == expected else 'MISMATCH'
        print(f'  0x{i:08x}: expected=0x{expected:08x} actual=0x{actual:08x} {status}')

    print('Resetting...')
    ocd(sock, 'reset run')
    sock.close()
    print('Done!')

if __name__ == '__main__':
    main()
