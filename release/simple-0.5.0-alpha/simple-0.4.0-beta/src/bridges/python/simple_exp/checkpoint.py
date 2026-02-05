"""SimpleCheckpointIO - Registers checkpoints as artifacts in .exp/ format."""

from __future__ import annotations

import hashlib
import os
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional, Union

try:
    from lightning.pytorch.plugins.io import CheckpointIO
except ImportError:
    try:
        from pytorch_lightning.plugins.io import CheckpointIO
    except ImportError:
        raise ImportError(
            "PyTorch Lightning is required. Install with: pip install lightning"
        )

import torch


class SimpleCheckpointIO(CheckpointIO):
    """CheckpointIO that stores checkpoints as content-addressed artifacts.

    Saves checkpoints to .exp/blobs/ with SHA256 dedup and registers
    them in the run's artifacts.sdn.

    Usage:
        from simple_exp import SimpleCheckpointIO

        checkpoint_io = SimpleCheckpointIO(exp_dir=".exp", run_id=run_id)
        trainer = Trainer(plugins=[checkpoint_io])
    """

    def __init__(self, exp_dir: str = ".exp", run_id: Optional[str] = None):
        super().__init__()
        self._exp_dir = Path(exp_dir)
        self._run_id = run_id

    def save_checkpoint(
        self,
        checkpoint: Dict[str, Any],
        path: Union[str, Path],
        storage_options: Optional[Any] = None,
    ) -> None:
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)

        # Save checkpoint to the requested path
        torch.save(checkpoint, path)

        # Also store as content-addressed blob
        blob_hash = self._store_as_blob(path)

        # Register in artifacts.sdn
        if self._run_id:
            self._register_artifact(
                name=path.name,
                blob_hash=blob_hash,
                kind="checkpoint",
                metadata={"step": str(checkpoint.get("global_step", 0))},
            )

    def load_checkpoint(
        self,
        path: Union[str, Path],
        map_location: Optional[Any] = None,
        storage_options: Optional[Any] = None,
    ) -> Dict[str, Any]:
        return torch.load(path, map_location=map_location)

    def remove_checkpoint(self, path: Union[str, Path]) -> None:
        path = Path(path)
        if path.exists():
            path.unlink()

    def _store_as_blob(self, path: Path) -> str:
        data = path.read_bytes()
        blob_hash = hashlib.sha256(data).hexdigest()
        prefix = blob_hash[:2]
        blob_dir = self._exp_dir / "blobs" / prefix
        blob_dir.mkdir(parents=True, exist_ok=True)
        blob_path = blob_dir / blob_hash
        if not blob_path.exists():
            shutil.copy2(path, blob_path)
        return blob_hash

    def _register_artifact(
        self,
        name: str,
        blob_hash: str,
        kind: str,
        metadata: Dict[str, str],
    ) -> None:
        if not self._run_id:
            return

        run_dir = self._exp_dir / "runs" / self._run_id
        artifacts_path = run_dir / "artifacts.sdn"

        meta_parts = [f'{k}="{v}"' for k, v in metadata.items()]
        meta_str = ", ".join(meta_parts)
        ts = datetime.now(timezone.utc).isoformat()
        line = f'  {name}: hash="{blob_hash}", kind="{kind}", time="{ts}", {meta_str}\n'

        with open(artifacts_path, "a") as f:
            f.write(line)
