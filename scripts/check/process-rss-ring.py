"""Read-only bounded /proc telemetry; never an admission or enforcement owner."""
from collections import deque
import json
import os
from pathlib import Path
import threading
import time


class ProcessRssRing:
    def __init__(self, pid, output):
        self.pid, self.output = pid, Path(output)
        self.done = threading.Event()
        self.rows = deque(maxlen=32)
        self.thread = threading.Thread(target=self.run, daemon=True)

    def start(self):
        self.thread.start()

    def stop(self):
        self.done.set()
        self.thread.join(timeout=5)

    def sample(self):
        processes = {}
        for entry in Path('/proc').iterdir():
            if not entry.name.isdigit():
                continue
            try:
                stat = (entry/'stat').read_text()
                close = stat.rfind(')')
                fields = stat[close+2:].split()
                processes[int(entry.name)] = {
                    'pid': int(entry.name), 'ppid': int(fields[1]),
                    'start_ticks': int(fields[19]),
                    'rss_kib': int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024,
                    'comm': stat[stat.index('(')+1:close][:120]}
            except (OSError, ValueError, IndexError):
                continue
        selected = {self.pid}
        for _ in range(256):
            children = {pid for pid, row in processes.items() if row['ppid'] in selected}
            expanded = selected | children
            if len(expanded) > 256 or expanded == selected:
                break
            selected = expanded
        rows = [processes[pid] for pid in sorted(selected) if pid in processes]
        return {'time_unix': time.time(), 'processes': rows,
                'observed_tree_rss_kib': sum(row['rss_kib'] for row in rows),
                'truncated': len(expanded) > 256}

    def run(self):
        while True:
            try:
                self.rows.append(self.sample())
                temporary = self.output.with_suffix('.tmp')
                temporary.write_text(json.dumps({'scope': 'read-only watchdog descendants; not enforcement',
                    'interval_seconds': 2, 'max_snapshots': 32, 'max_processes': 256,
                    'samples': list(self.rows)}, indent=2))
                temporary.replace(self.output)
            except Exception as error:
                self.output.with_suffix('.error').write_text(str(error))
                return
            if self.done.wait(2):
                return
