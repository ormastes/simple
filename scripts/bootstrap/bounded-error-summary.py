#!/usr/bin/env python3
"""Summarize compiler output without retaining unbounded diagnostic lines.

The original log remains authoritative. Offsets, byte count and SHA-256 bind
the bounded display to that log; truncation never changes the compiler exit.
"""
import hashlib
import re
from collections import deque
from pathlib import Path

CHUNK = 64 * 1024
LINE_BYTES = 512
ERROR_LINES = 16
ERROR = re.compile(rb'error:|\[FAIL\]|failed:|access violation', re.I)
PHASE = re.compile(rb'\[build\] phase=([a-z_]+)')
LINK = re.compile(rb'linker command failed|lld-link[^\r\n]{0,128}error|undefined reference', re.I)


def summarize(path):
    path = Path(path)
    digest = hashlib.sha256()
    errors = deque(maxlen=ERROR_LINES)
    size = offset = length = 0
    head = tail = scan_tail = b''
    is_error = link = access = False
    phase = None
    truncated = 0

    def finish():
        nonlocal offset, length, head, tail, scan_tail, is_error, truncated
        if is_error:
            cut = length > LINE_BYTES
            text = head if not cut else head[:LINE_BYTES // 2] + b' ... [truncated; see original log] ... ' + tail
            errors.append(dict(offset=offset, bytes=length, truncated=cut,
                               text=text.decode('utf-8', errors='replace')))
            truncated += int(cut)
        offset += length + 1
        length = 0
        head = tail = scan_tail = b''
        is_error = False

    with path.open('rb') as stream:
        while block := stream.read(CHUNK):
            size += len(block)
            digest.update(block)
            pieces = block.split(b'\n')
            for index, piece in enumerate(pieces):
                window = scan_tail + piece
                # Scan complete bounded chunks, including overlap for markers
                # crossing read boundaries; never regex the entire long line.
                is_error = is_error or ERROR.search(window) is not None
                access = access or b'0xC0000005' in window
                prefix = (head + piece)[:8].lower()
                link = link or LINK.search(window) is not None or prefix.startswith((b'linking:', b'linked:'))
                for match in PHASE.finditer(window):
                    # A phase split at the end of a chunk is rescanned with
                    # the next chunk, replacing its incomplete prefix.
                    phase = match.group(1).decode('ascii')
                head = (head + piece)[:LINE_BYTES]
                tail = (tail + piece)[-LINE_BYTES // 2:]
                scan_tail = window[-256:]
                length += len(piece)
                if index < len(pieces) - 1:
                    finish()
        if length:
            finish()
    return dict(log_path=str(path), log_bytes=size, log_sha256=digest.hexdigest(),
                last_reported_phase=phase, link_reached=link,
                native_access_violation=access, error_lines=[r['text'] for r in errors],
                error_locations=list(errors), truncated_error_lines=truncated)
