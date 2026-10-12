"""Exercise focused composition admission against real files and corruptions."""
import hashlib
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_fields(path, fields):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(f"{key}={value}\n" for key, value in fields.items()), encoding="utf-8", newline="\n")


class FocusedCompositionBindings(unittest.TestCase):
    def test_real_compositions_and_admitted_receipt_reject_tampering(self):
        mutations = ("none", "k1", "cuda", "manifest", "digest", "receipt_status", "receipt_transcript", "duplicate_policy", "extra_module")
        selected = os.environ.get("SIMPLE_COMPOSITION_BINDING_CASE")
        if selected:
            self.assertIn(selected, mutations)
            mutations = (selected,)
        for mutation in mutations:
            # The production hash-named CUDA path is long; use the central
            # short storage root on Windows rather than the user's Temp prefix.
            storage = Path(ROOT.anchor) / "dev/simple-bootstrap-storage" if os.name == "nt" else None
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory(prefix="i6f-", dir=storage) as directory:
                root = Path(directory)
                k1 = root / "src/compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl"
                template = root / "src/compositions/cuda_disabled/plugins/backend_registry/selected_cuda_backend.spl"
                manifest = root / "src/compiler/simple.sdn"
                for path, content in ((k1, "selected K1 bytes\n"), (template, "disabled CUDA bytes\n"), (manifest, "compiler_backends:\n  cuda:\n    enabled: false\n    placement: dynamic\n")):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content, encoding="utf-8", newline="\n")
                cuda = root / f"build/compositions/cuda-{digest(manifest)}-{digest(template)}/plugins/backend_registry/selected_cuda_backend.spl"
                cuda.parent.mkdir(parents=True)
                cuda.write_bytes(template.read_bytes())
                receipt = root / "build/logs/x86_64-pc-windows-msvc/stage2-stage3-k1-composition.env"
                receipt_fields = dict(schema="simple-bootstrap-k1-composition-receipt-v1", status="pass", policy="llvm-cranelift", selected_composition_sha256=digest(k1))
                map_fields = {}
                for phase in ("stage2", "stage3"):
                    for kind, role in (("transcript", "command_transcript"), ("log", "build_log")):
                        sha = hashlib.sha256(f"{phase}:{kind}".encode()).hexdigest()
                        receipt_fields[f"{phase}_{kind}_sha256"] = sha
                        map_fields[f"{phase}_{role}_sha256"] = sha
                write_fields(receipt, receipt_fields)
                bindings = dict(focused_k1_policy="llvm-cranelift", focused_k1_sha256=digest(k1), focused_cuda_manifest_sha256=digest(manifest), focused_cuda_template_sha256=digest(template), focused_k1_receipt_sha256=digest(receipt))
                if mutation == "k1": k1.write_text("changed K1\n")
                if mutation == "cuda": cuda.write_text("changed generated CUDA\n")
                if mutation == "extra_module": (cuda.parent / "injected.spl").write_text("unexpected module\n")
                if mutation == "manifest": manifest.write_text(manifest.read_text().replace("false", "true"))
                if mutation == "digest": bindings["focused_k1_sha256"] = "bad"
                if mutation in ("receipt_status", "receipt_transcript"):
                    receipt_fields["status" if mutation == "receipt_status" else "stage3_transcript_sha256"] = "fail" if mutation == "receipt_status" else "0" * 64
                    write_fields(receipt, receipt_fields)
                    # Re-signing a receipt hash cannot authorize its wrong contents.
                    bindings["focused_k1_receipt_sha256"] = digest(receipt)
                write_fields(root / "bindings.env", bindings)
                if mutation == "duplicate_policy":
                    with (root / "bindings.env").open("a", newline="\n") as stream: stream.write("focused_k1_policy=llvm\n")
                write_fields(root / "map.env", map_fields)
                modules = "\n".join(f". {shlex.quote(str(ROOT / 'scripts/check/lib/bootstrap-stage3' / (name + '.shs')))}" for name in ("authority", "command-snapshot", "manifest-verify"))
                script = modules + """
bootstrap_stage3_root=$(pwd -P)
bootstrap_stage3_manifest_output_root=$bootstrap_stage3_root/build
bootstrap_stage3_manifest=$bootstrap_stage3_root/bindings.env
bootstrap_stage3_manifest_descriptor_mode=0
bootstrap_stage3_platform=x86_64-pc-windows-msvc
bootstrap_stage3_map_value() { bootstrap_stage3_manifest_value "$1" "$bootstrap_stage3_root/map.env"; }
bootstrap_stage3_focused_compositions_verify
"""
                result = subprocess.run(["sh", "-c", script], cwd=root, text=True, capture_output=True, timeout=30)
                self.assertEqual(result.returncode == 0, mutation == "none", result.stderr)


if __name__ == "__main__":
    unittest.main()
