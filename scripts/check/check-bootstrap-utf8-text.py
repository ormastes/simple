#!/usr/bin/env python3
"""Exercise actual helper text-I/O sites under a simulated CP949 default.

No compiler subprocess or existing native acceptance criteria are rerun.
"""
import ast
import hashlib
import io
from pathlib import Path
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
HELPERS = [
    "scripts/check/check-native-build-cache-binding.py",
    "scripts/bootstrap/check-stage2-sanity-log-retention.shs",
]

def main():
    checked = 0
    original_open = io.open
    def cp949_default(file, mode="r", buffering=-1, encoding=None, *args, **kwargs):
        if "b" not in mode and encoding in (None, "locale"):
            encoding = "cp949"
        return original_open(file, mode, buffering, encoding, *args, **kwargs)
    with tempfile.TemporaryDirectory(prefix="utf8-helper-") as temporary:
        target = Path(temporary) / "한글-😀.txt"
        sample = "한글 é 😀"
        for helper in HELPERS:
            source = (ROOT / helper).read_text(encoding="utf-8")
            if helper.endswith(".shs"):
                source = source.split("<<'PY'\n", 1)[1].rsplit("\nPY", 1)[0]
            tree = ast.parse(source)
            for call in ast.walk(tree):
                if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Attribute):
                    continue
                method = call.func.attr
                if method not in ("read_text", "write_text", "open"):
                    continue
                assert any(k.arg == "encoding" and isinstance(k.value, ast.Constant)
                           and k.value.value == "utf-8" for k in call.keywords), (helper, call.lineno)
                # Run the actual site's receiver method and keyword arguments,
                # replacing only its path and content with adversarial fixture data.
                fixture = ast.Call(ast.Attribute(ast.Name("target", ast.Load()), method, ast.Load()),
                                   [ast.Constant(sample)] if method == "write_text" else
                                   [ast.Constant("w")] if method == "open" else [], call.keywords)
                expression = compile(ast.fix_missing_locations(ast.Expression(fixture)), helper, "eval")
                target.write_bytes(sample.encode("utf-8"))
                with patch("io.open", cp949_default):
                    result = eval(expression, {"target": target})
                    if method == "read_text":
                        assert result == sample
                        target.write_bytes(b"\xff")
                        try:
                            eval(expression, {"target": target})
                        except UnicodeDecodeError:
                            pass
                        else:
                            raise AssertionError("malformed UTF-8 accepted")
                    elif method == "open":
                        with result as stream:
                            stream.write(sample)
                    if method != "read_text":
                        assert target.read_bytes() == sample.encode("utf-8")
                checked += 1
            for call in ast.walk(tree):
                if isinstance(call, ast.Call) and any(k.arg == "text" and isinstance(k.value, ast.Constant)
                                                      and k.value.value is True for k in call.keywords):
                    assert any(k.arg == "encoding" and isinstance(k.value, ast.Constant)
                               and k.value.value == "utf-8" for k in call.keywords)
        # The actual nested source reader must retain its original digest semantics.
        tree = ast.parse((ROOT / HELPERS[0]).read_text(encoding="utf-8"))
        reader = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == "read")
        namespace = {"args": SimpleNamespace(repo=Path(temporary)), "originals": {}, "hashlib": hashlib}
        exec(compile(ast.fix_missing_locations(ast.Module([reader], type_ignores=[])), HELPERS[0], "exec"), namespace)
        target.write_bytes(sample.encode("utf-8"))
        with patch("io.open", cp949_default):
            assert namespace["read"](target.name) == sample
        assert namespace["originals"][target.name] == hashlib.sha256(sample.encode("utf-8")).hexdigest()
    print(f"PASS: {checked} actual text-I/O sites; CP949 default, Unicode path/content, strict malformed rejection, source digest")

if __name__ == "__main__":
    main()
