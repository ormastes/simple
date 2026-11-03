#!/usr/bin/env python3
"""Native C HTTP framing: byte-exact loopback responses, no external services."""
import argparse
import hashlib
from pathlib import Path
import socket
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    exe = out / 'http-framing'
    cmd = ['cc', '-O2', '-ffunction-sections', '-fdata-sections', '-std=gnu11',
           '-DSIMPLE_CORE_C_STANDALONE=1', '-DSIMPLE_RUNTIME_MEMORY_OWNER=1',
           '-I' + str(ROOT / 'src/runtime'), '-I' + str(ROOT / 'src/runtime/platform'),
           str(ROOT / 'src/runtime/test/rt_http_framing_selfcheck.c'),
           '-Wl,--gc-sections', '-lm', '-lpthread', '-o', str(exe)]
    with (out / 'compile.log').open('wb') as log:
        subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=120)
    binary = b'\x00\x7f\x80\xff'
    cases = [
        ('length-binary', b'Content-Length: 4', binary, binary),
        ('length-empty', b'Content-Length: 0', b'', b''),
        ('length-short', b'Content-Length: 5', binary, None),
        ('length-overflow', b'Content-Length: 18446744073709551616', b'', None),
        ('length-negative', b'Content-Length: -1', b'', None),
        ('length-suffix', b'Content-Length: 4x', binary, None),
        ('length-duplicate-same', b'Content-Length: 4\r\nContent-Length: 4', binary, binary),
        ('length-duplicate-conflict', b'Content-Length: 4\r\nContent-Length: 5', binary, None),
        ('chunk-binary', b'Transfer-Encoding: chunked', b'4\r\n' + binary + b'\r\n0\r\n\r\n', binary),
        ('chunk-empty', b'Transfer-Encoding: chunked', b'0\r\n\r\n', b''),
        ('chunk-extensions-trailer', b'Transfer-Encoding: chunked', b'1;foo=bar\r\na\r\n0\r\nX-End: yes\r\n\r\n', b'a'),
    ]
    for name, body in [
        ('missing-zero', b'1\r\na\r\n'), ('missing-final-crlf', b'0\r\n'),
        ('empty-wire', b''), ('size-suffix', b'1z\r\na\r\n0\r\n\r\n'),
        ('size-sign', b'+1\r\na\r\n0\r\n\r\n'), ('size-space', b' 1\r\na\r\n0\r\n\r\n'),
        ('size-prefix', b'0x1\r\na\r\n0\r\n\r\n'),
        ('size-overflow', b'10000000000000000\r\na\r\n0\r\n\r\n'),
        ('trailer-truncated', b'0\r\nX-End: yes\r\n'),
    ]:
        cases.append(('chunk-' + name, b'Transfer-Encoding: chunked', body, None))
    full = b'4\r\n' + binary + b'\r\n0\r\n\r\n'
    for end in range(1, len(full)):
        cases.append(('chunk-prefix-' + str(end), b'Transfer-Encoding: chunked', full[:end], None))
    results = []
    for name, headers, body, expected in cases:
        for stride in (1, 7, 4096):
            listener = socket.socket()
            listener.bind(('127.0.0.1', 0))
            listener.listen(1)
            listener.settimeout(5)
            port = listener.getsockname()[1]
            wire = b'HTTP/1.1 200 OK\r\n' + headers + b'\r\nConnection: close\r\n\r\n' + body
            errors = []
            def serve():
                try:
                    with listener:
                        conn, _ = listener.accept()
                        with conn:
                            conn.settimeout(5)
                            request = b''
                            while b'\r\n\r\n' not in request:
                                part = conn.recv(4096)
                                if not part: raise RuntimeError('request truncated')
                                request += part
                            for offset in range(0, len(wire), stride):
                                conn.sendall(wire[offset:offset + stride])
                                if stride < 4096: time.sleep(0.0002)
                except Exception as error:
                    errors.append(str(error))
            thread = threading.Thread(target=serve)
            thread.start()
            run = subprocess.run([str(exe), 'http://127.0.0.1:' + str(port) + '/'], capture_output=True, timeout=8)
            thread.join(6)
            good = not errors and not thread.is_alive() and (
                (run.returncode == 2 and not run.stdout and bool(run.stderr)) if expected is None
                else (run.returncode == 0 and run.stdout == expected))
            results.append(f'{"PASS" if good else "FAIL"} {name} stride={stride} rc={run.returncode} body={run.stdout.hex()} error={run.stderr.decode(errors="replace").strip()}')
    (out / 'results.txt').write_text('\n'.join(results) + '\n')
    for path in (ROOT / 'src/runtime/runtime_native.c', ROOT / 'src/runtime/test/rt_http_framing_selfcheck.c', exe):
        print('SHA256', hashlib.sha256(path.read_bytes()).hexdigest(), path)
    failures = [line for line in results if line.startswith('FAIL')]
    print('\n'.join(failures[:20]))
    print(f'cases={len(results)} passed={len(results) - len(failures)} failed={len(failures)}')
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()
