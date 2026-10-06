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

# Capture compiler diagnostic events before head/tail retention drops the middle.
# The compiler may concatenate phase and fatal messages without a newline.
EVENT = re.compile(rb'error\[[a-z0-9_-]{1,32}\]:|\[ERROR\]|\[hir-fatal\]|\[hir-owner-fatal\]|\[hir-fatal-count\]|error:|\[FAIL\]|failed:|access violation|\[BOOTSTRAP-PHASE\]|\[build\]|\[hir-shard\]|\r?\n', re.I)
BOUNDARIES = {b'[bootstrap-phase]', b'[build]', b'[hir-shard]', b'\n', b'\r\n'}


class DiagnosticStreamSummary:
    """Bounded event excerpts, offsets and counts; never a compiler verdict.

    `events_observed` counts markers, not distinct failures. Dropped excerpts
    and truncated events are explicit. This collector never buffers a line.
    """
    def __init__(self, max_events=64, event_bytes=1024):
        if not 1 <= max_events <= 256 or not 64 <= event_bytes <= 4096:
            raise ValueError('Diagnostic summary limits outside bounded range')
        self.max_events, self.event_bytes = max_events, event_bytes
        self.records = deque(maxlen=max_events)
        # Fixed marker taxonomy; no map keyed by unbounded error codes.
        self.marker_counts = {}
        self.samples = {}
        self.sample_capacity = min(max_events, 16)
        self.sample_overflow_events = 0
        self.digest = hashlib.sha256()
        self.seen = self.offset = self.events = self.truncated = 0
        self.carry = b''
        self.active = None
        self.closed = False

    def _append(self, data):
        if self.active is not None:
            self.active['bytes'] += len(data)
            self.active['digest'].update(data)
            room = self.event_bytes - len(self.active['excerpt'])
            if room > 0:
                self.active['excerpt'] += data[:room]

    def _finish_event(self):
        if self.active is None:
            return
        row = self.active
        row['truncated'] = row['bytes'] > len(row['excerpt'])
        self.truncated += int(row['truncated'])
        row['text'] = row.pop('excerpt').decode('utf-8', errors='replace')
        row['event_sha256'] = row.pop('digest').hexdigest()
        key = row['event_sha256']
        if key in self.samples:
            self.samples[key]['occurrences'] += 1
        elif len(self.samples) < self.sample_capacity:
            self.samples[key] = dict(row, occurrences=1, text=row['text'][:256],
                                     truncated=row['truncated'] or len(row['text']) > 256)
        else:
            # Count events, not distinct fingerprints or distinct causes.
            self.sample_overflow_events += 1
        self.records.append(row)
        self.active = None

    def _scan(self, final=False):
        end = len(self.carry) if final else max(0, len(self.carry) - 128)
        # Never split a complete token across the processed/carry boundary.
        for match in EVENT.finditer(self.carry):
            if match.start() < end < match.end():
                end = match.start()
                break
        data = self.carry[:end]
        cursor = 0
        for match in EVENT.finditer(data):
            self._append(data[cursor:match.start()])
            self._finish_event()
            token = match.group()
            if token.lower() not in BOUNDARIES:
                self.events += 1
                category = 'error[code]:' if token.lower().startswith(b'error[') else token.decode('ascii').lower()
                self.marker_counts[category] = self.marker_counts.get(category, 0) + 1
                self.active = dict(offset=self.offset + match.start(), marker=token.decode('ascii'), bytes=0, excerpt=b'', digest=hashlib.sha256())
                self._append(token)
            cursor = match.end()
        self._append(data[cursor:])
        self.offset += end
        self.carry = self.carry[end:]

    def feed(self, block):
        if self.closed:
            raise RuntimeError('Diagnostic collector already finished')
        self.seen += len(block)
        self.digest.update(block)
        # Bound transient memory even if a caller hands us a giant block.
        for start in range(0, len(block), CHUNK):
            self.carry += block[start:start + CHUNK]
            self._scan()

    def finish(self):
        if not self.closed:
            self._scan(final=True)
            self._finish_event()
            self.closed = True
        return dict(schema='bounded-live-diagnostic-events-v1', stream_bytes=self.seen,
                    stream_sha256=self.digest.hexdigest(), events_observed=self.events,
                    events_retained=len(self.records), events_dropped=self.events-len(self.records),
                    truncated_events=self.truncated, max_events=self.max_events,
                    event_bytes=self.event_bytes, records=list(self.records),
                    marker_counts=dict(self.marker_counts),
                    count_scope='exact recognized markers in received stream; not distinct failures',
                    sample_policy='first full-event SHA256 fingerprints, bounded; occurrences exact for retained fingerprints',
                    sample_capacity=self.sample_capacity, representative_samples=list(self.samples.values()),
                    sample_overflow_events=self.sample_overflow_events,
                    cause_inventory_complete=False,
                    qualification='OBSERVATION_ONLY_NOT_A_VERDICT')


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
