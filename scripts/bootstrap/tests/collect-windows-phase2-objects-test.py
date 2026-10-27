"""Focused, compiler-free regression tests for the Windows Phase2 collector."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import tempfile
import threading
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "collect-windows-phase2-objects.py"
SPEC = importlib.util.spec_from_file_location("phase2_object_collector", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
COLLECTOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COLLECTOR)


class WatchdogClassificationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.rss = {
            "status": "session-helper-install-failed",
            "exit_status": "89",
            "root_pid": "0",
            "samples": "0",
        }
        self.refusal = (
            "rss-guard: session installation failed: cannot record compiler identity "
            "at process-tree-rss-watchdog.pl line 825."
        )

    def test_requires_exact_precompiler_setup_evidence(self) -> None:
        classify = COLLECTOR.classify_watchdog_setup_failure_v1
        self.assertTrue(classify(89, self.refusal, self.rss, False))
        self.assertFalse(classify(89, "unrelated watchdog error", self.rss, False))
        self.assertFalse(classify(89, self.refusal, {**self.rss, "root_pid": "412"}, False))
        self.assertFalse(classify(89, self.refusal, {**self.rss, "samples": "1"}, False))
        self.assertFalse(classify(89, self.refusal, self.rss, True))
        self.assertFalse(classify(1, self.refusal, self.rss, False))


class LogExcerptTests(unittest.TestCase):
    def test_excerpt_keeps_terminal_diagnostic_after_progress_flood(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "compiler.log"
            path.write_text(
                "[build] phase=parse state=running current=early\n" +
                ("[build] phase=hir state=running current=progress\n" * 5000) +
                "[ERROR] HIR lowering failed: unresolved name final_symbol\n" +
                "error: final terminal diagnostic context\n",
                encoding="utf-8",
            )
            excerpt = COLLECTOR.log_excerpt(path)
            self.assertLessEqual(len(excerpt), 4096)
            self.assertIn("HEAD:", excerpt)
            self.assertIn("unresolved name final_symbol", excerpt)
            self.assertIn("final terminal diagnostic context", excerpt)


class CoffSectionBoundsTests(unittest.TestCase):
    @staticmethod
    def _standard_object(raw_size: int, raw_pointer: int,
                         characteristics: int = 0) -> bytes:
        file_header = ((0x8664).to_bytes(2, "little") + (1).to_bytes(2, "little") +
                       b"\0" * 12 + b"\0\0" + b"\0\0")
        section = bytearray(40)
        section[16:20] = raw_size.to_bytes(4, "little")
        section[20:24] = raw_pointer.to_bytes(4, "little")
        section[36:40] = characteristics.to_bytes(4, "little")
        return file_header + bytes(section)

    @staticmethod
    def _bigobj(raw_size: int, raw_pointer: int) -> bytes:
        guid = bytes.fromhex("c7a1bad1eeba a94baf20faf66aa4dcb8".replace(" ", ""))
        header = (b"\0\0\xff\xff" + (2).to_bytes(2, "little") +
                  (0x8664).to_bytes(2, "little") + b"\0" * 4 + guid +
                  b"\0" * 16 + (1).to_bytes(4, "little") + b"\0" * 8)
        section = bytearray(40)
        section[16:20] = raw_size.to_bytes(4, "little")
        section[20:24] = raw_pointer.to_bytes(4, "little")
        return header + bytes(section)

    def test_rejects_out_of_bounds_standard_and_bigobj_raw_data_but_accepts_bss(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            malformed = [
                ("standard.obj", self._standard_object(1, 60)),
                ("bigobj.obj", self._bigobj(4, 94)),
            ]
            for name, content in malformed:
                path = base / name
                path.write_bytes(content)
                with self.subTest(name=name), self.assertRaises(COLLECTOR.Refusal):
                    COLLECTOR.validate_amd64_coff(path)

            bss = base / "valid-bss.obj"
            bss.write_bytes(self._standard_object(16, 0, 0x00000080))
            size, kind = COLLECTOR.validate_amd64_coff(bss)
            self.assertEqual((size, kind), (60, "COFF_AMD64"))


class StopRequestTests(unittest.TestCase):
    def test_concurrent_dispatch_reserves_every_row_once(self) -> None:
        entries = [{"id": f"row-{index}"} for index in range(120)]
        cursor_state = [0]
        cursor_lock = threading.Lock()
        seen_lock = threading.Lock()
        stop = threading.Event()
        seen: list[str] = []
        with tempfile.TemporaryDirectory() as temporary:
            sentinel = Path(temporary) / COLLECTOR.STOP_REQUEST_NAME

            def dispatch() -> None:
                while True:
                    row, _ = COLLECTOR.take_dispatch_row(
                        entries, cursor_state, cursor_lock, stop, 10.0,
                        sentinel, now=1.0)
                    if row is None:
                        return
                    with seen_lock:
                        seen.append(str(row["id"]))

            lanes = [threading.Thread(target=dispatch) for _ in range(2)]
            for lane in lanes:
                lane.start()
            for lane in lanes:
                lane.join()
        self.assertEqual(cursor_state[0], len(entries))
        self.assertEqual(len(seen), len(entries))
        self.assertEqual(set(seen), {str(row["id"]) for row in entries})

    def test_stop_sentinel_does_not_advance_cursor_or_cancel_dispatched_row(self) -> None:
        entries = [{"id": f"row-{index}"} for index in range(12)]
        lock = threading.Lock()
        stop = threading.Event()
        cursor_state = [0]
        with tempfile.TemporaryDirectory() as temporary:
            sentinel = Path(temporary) / COLLECTOR.STOP_REQUEST_NAME
            active, requested = COLLECTOR.take_dispatch_row(
                entries, cursor_state, lock, stop, 10.0, sentinel, now=1.0)
            self.assertEqual(active, entries[0])
            self.assertEqual(cursor_state[0], 1)
            self.assertFalse(requested)
            release_active = threading.Event()
            active_finished = threading.Event()
            active_job = threading.Thread(
                target=lambda: (release_active.wait(), active_finished.set()))
            active_job.start()
            sentinel.touch()
            next_row, requested = COLLECTOR.take_dispatch_row(
                entries, cursor_state, lock, stop, 10.0, sentinel, now=2.0)
            self.assertIsNone(next_row)
            self.assertEqual(cursor_state[0], 1)
            self.assertTrue(requested)
            self.assertTrue(stop.is_set())
            self.assertTrue(active_job.is_alive())
            release_active.set()
            active_job.join(timeout=1)
            self.assertTrue(active_finished.is_set())


class PriorityManifestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        inventory = os.environ.get("SIMPLE_PHASE2_REAL_INVENTORY")
        cohort = os.environ.get("SIMPLE_PHASE2_REAL_PRIORITY_MANIFEST")
        if not inventory or not cohort:
            raise unittest.SkipTest("set real frozen inventory/cohort paths for full partition test")
        cls.inventory_path = Path(inventory)
        cls.cohort_path = Path(cohort)
        cls.attempts_path = (Path(os.environ["SIMPLE_PHASE2_REAL_ATTEMPTS"])
                             if os.environ.get("SIMPLE_PHASE2_REAL_ATTEMPTS") else None)
        cls.inventory_sha = COLLECTOR.hash_file(cls.inventory_path)
        _, cls.rows = COLLECTOR.load_inventory(cls.inventory_path)

    def _copy_cohort(self, text: str, temporary: str, name: str) -> Path:
        path = Path(temporary) / name
        path.write_text(text, encoding="utf-8")
        return path

    def test_real_cohort_prioritizes_165_without_dropping_any_inventory_row(self) -> None:
        ordered = COLLECTOR.apply_priority_manifest(
            self.rows, self.cohort_path, self.inventory_sha)
        self.assertEqual(len(ordered), 14978)
        self.assertEqual(len({str(row["id"]) for row in ordered}), 14978)
        self.assertEqual(
            [str(row["canonical_source"]) for row in ordered[:165]],
            [str(row["canonical_source"]) for row in self.rows
             if str(row["canonical_source"]).startswith(tuple(
                 root for root, _ in COLLECTOR.TOOLING_PRIORITY_ROOT_COUNTS))],
        )

    def test_rejects_wrong_inventory_hash_duplicate_id_and_missing_row(self) -> None:
        original = self.cohort_path.read_text(encoding="utf-8")
        header, collections = COLLECTOR.parse_sdn(self.cohort_path)
        priority = collections["priority_rows"]
        first_id = COLLECTOR.unq(priority[0]["row_id"])
        second_id = COLLECTOR.unq(priority[1]["row_id"])

        with tempfile.TemporaryDirectory() as temporary:
            bad_hash = original.replace(
                f'inventory_sha256: "{self.inventory_sha}"',
                'inventory_sha256: "' + "0" * 64 + '"', 1)
            path = self._copy_cohort(bad_hash, temporary, "bad-hash.sdn")
            with self.assertRaises(COLLECTOR.Refusal):
                COLLECTOR.apply_priority_manifest(self.rows, path, self.inventory_sha)

            duplicate = original.replace(
                f'row_id: "{second_id}"', f'row_id: "{first_id}"', 1)
            path = self._copy_cohort(duplicate, temporary, "duplicate-id.sdn")
            with self.assertRaises(COLLECTOR.Refusal):
                COLLECTOR.apply_priority_manifest(self.rows, path, self.inventory_sha)

            lines = original.splitlines()
            last_record = max(i for i, line in enumerate(lines) if line.startswith("  - row_id:"))
            path = self._copy_cohort("\n".join(lines[:last_record]) + "\n",
                                     temporary, "missing-row.sdn")
            with self.assertRaises(COLLECTOR.Refusal):
                COLLECTOR.apply_priority_manifest(self.rows, path, self.inventory_sha)

    def test_real_valid_pass_proof_survives_repeated_resume_state_selection(self) -> None:
        if self.attempts_path is None:
            self.skipTest("set SIMPLE_PHASE2_REAL_ATTEMPTS to test a retained real PASS receipt")
        events = COLLECTOR.load_attempt_events(self.attempts_path)
        latest, counts = COLLECTOR.index_attempt_events(events)
        row_by_id = {str(row["id"]): row for row in self.rows}
        selected = None
        for row_id, event in latest.items():
            if event.get("status") != "PASS" or row_id not in row_by_id:
                continue
            object_path = Path(str(event.get("object_path", "")))
            try:
                object_bytes, _ = COLLECTOR.validate_amd64_coff(object_path)
            except (OSError, COLLECTOR.Refusal):
                continue
            if (object_bytes == event.get("object_bytes") and
                    COLLECTOR.hash_file(object_path) == event.get("object_sha256")):
                selected = row_id, event
                break
        if selected is None:
            self.skipTest("no retained PASS receipt has a present matching AMD64 COFF object")

        row_id, receipt = selected
        row = row_by_id[row_id]
        attempt_count = counts[row_id]
        for _ in range(2):
            self.assertEqual(COLLECTOR.pending_state_rows([row], {row_id: "PASS"}), [])
            latest_after, counts_after = COLLECTOR.index_attempt_events(events)
            self.assertEqual(latest_after[row_id], receipt)
            self.assertEqual(latest_after[row_id].get("object_path"), receipt.get("object_path"))
            self.assertEqual(latest_after[row_id].get("object_sha256"), receipt.get("object_sha256"))
            self.assertEqual(counts_after[row_id], attempt_count)

if __name__ == "__main__":
    unittest.main()
