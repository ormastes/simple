"""SimpleLogger - PyTorch Lightning Logger that writes to .exp/ format."""

from __future__ import annotations

import hashlib
import json
import os
import socket
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

try:
    from lightning.pytorch.loggers.logger import Logger, rank_zero_experiment
    from lightning.pytorch.utilities import rank_zero_only
except ImportError:
    try:
        from pytorch_lightning.loggers.logger import Logger, rank_zero_experiment
        from pytorch_lightning.utilities import rank_zero_only
    except ImportError:
        raise ImportError(
            "PyTorch Lightning is required. Install with: pip install lightning"
        )


class SimpleLogger(Logger):
    """Logger that writes metrics and hparams to .exp/ directory format.

    Compatible with the Simple language experiment tracking library.

    Usage:
        from simple_exp import SimpleLogger

        logger = SimpleLogger(exp_dir=".exp", tags=["baseline"])
        trainer = Trainer(logger=logger)
        trainer.fit(model, datamodule)
    """

    def __init__(
        self,
        exp_dir: str = ".exp",
        tags: Optional[List[str]] = None,
        name: str = "default",
    ):
        super().__init__()
        self._exp_dir = Path(exp_dir)
        self._tags = tags or []
        self._name = name
        self._run_id: Optional[str] = None
        self._run_dir: Optional[Path] = None
        self._hparams: Dict[str, Any] = {}
        self._step = 0

    @property
    def name(self) -> str:
        return self._name

    @property
    def version(self) -> str:
        return self._run_id or "unknown"

    @property
    @rank_zero_experiment
    def experiment(self) -> "SimpleLogger":
        return self

    @property
    def run_id(self) -> Optional[str]:
        return self._run_id

    @rank_zero_only
    def log_hyperparams(self, params: Union[Dict[str, Any], Any]) -> None:
        if hasattr(params, "items"):
            self._hparams.update(params)
        elif hasattr(params, "__dict__"):
            self._hparams.update(vars(params))
        self._write_config()

    @rank_zero_only
    def log_metrics(
        self, metrics: Dict[str, float], step: Optional[int] = None
    ) -> None:
        if step is not None:
            self._step = step

        self._ensure_run()

        for name, value in metrics.items():
            self._append_event(
                kind="metric",
                data={"name": name, "value": str(value), "step": str(self._step)},
            )

    @rank_zero_only
    def finalize(self, status: str) -> None:
        if self._run_id is None:
            return

        run_status = "completed" if status == "success" else "failed"
        self._append_event(
            kind="end",
            data={"status": run_status},
        )
        self._write_meta(status=run_status)

    def _ensure_run(self) -> None:
        if self._run_id is not None:
            return

        self._init_dirs()
        self._run_id = self._generate_run_id()
        self._run_dir = self._exp_dir / "runs" / self._run_id
        self._run_dir.mkdir(parents=True, exist_ok=True)

        self._write_meta(status="running")
        self._write_config()
        self._append_event(
            kind="start",
            data={"config_hash": self._config_hash()},
        )

    def _init_dirs(self) -> None:
        self._exp_dir.mkdir(exist_ok=True)
        (self._exp_dir / "runs").mkdir(exist_ok=True)
        (self._exp_dir / "blobs").mkdir(exist_ok=True)

    def _generate_run_id(self) -> str:
        config_hash = self._config_hash()
        vcs_hash = self._get_vcs_hash()
        ts = datetime.now(timezone.utc).isoformat()
        combined = f"{config_hash}:{vcs_hash}:{ts}"
        return hashlib.sha256(combined.encode()).hexdigest()[:12]

    def _config_hash(self) -> str:
        serialized = json.dumps(self._hparams, sort_keys=True, default=str)
        return hashlib.sha256(serialized.encode()).hexdigest()

    def _get_vcs_hash(self) -> str:
        for cmd in [["jj", "log", "-r@", "--no-graph", "-T", "commit_id"], ["git", "rev-parse", "HEAD"]]:
            try:
                result = subprocess.run(
                    cmd, capture_output=True, text=True, timeout=5
                )
                if result.returncode == 0:
                    return result.stdout.strip()[:12]
            except (FileNotFoundError, subprocess.TimeoutExpired):
                continue
        return "unknown"

    def _write_meta(self, status: str) -> None:
        if self._run_dir is None:
            return

        lines = [
            "# Run metadata",
            f'run_id: "{self._run_id}"',
            f'status: "{status}"',
            f'start_time: "{datetime.now(timezone.utc).isoformat()}"',
            f'hostname: "{socket.gethostname()}"',
            f'vcs_hash: "{self._get_vcs_hash()}"',
            f'config_hash: "{self._config_hash()}"',
            f'tags: "{", ".join(self._tags)}"',
        ]
        (self._run_dir / "meta.sdn").write_text("\n".join(lines) + "\n")

    def _write_config(self) -> None:
        if self._run_dir is None:
            return

        lines = ["# Config snapshot"]
        for key, value in self._hparams.items():
            lines.append(f'{key}: "{value}"')
        (self._run_dir / "config.sdn").write_text("\n".join(lines) + "\n")

    def _append_event(self, kind: str, data: Dict[str, str]) -> None:
        if self._run_dir is None:
            return

        ts = datetime.now(timezone.utc).isoformat()
        parts = [f'timestamp: "{ts}"', f'kind: "{kind}"']
        for key, value in data.items():
            parts.append(f'data.{key}: "{value}"')

        line = ", ".join(parts) + "\n"
        events_path = self._run_dir / "events.sdnl"
        with open(events_path, "a") as f:
            f.write(line)
