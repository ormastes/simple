#!/usr/bin/env python3
"""Mach-O hosted-link capture: retain the real compiler driver's exact inputs."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def resolve_driver():
    driver = Path(os.path.abspath(shutil.which("clang")))
    # /usr/bin/clang dispatches through xcode-select; bind the real tool bytes.
    if driver == Path("/usr/bin/clang"):
        driver = Path(subprocess.check_output(["/usr/bin/xcrun", "--find", "clang"], text=True, timeout=10).strip()).resolve()
    if not driver.is_absolute() or not driver.is_file() or driver == Path("/usr/bin/clang"):
        raise ValueError("Darwin compiler driver did not resolve to a concrete tool")
    return driver


def resolve_sdk():
    sdk = Path(subprocess.check_output(["/usr/bin/xcrun", "--show-sdk-path"], text=True, timeout=10).strip()).resolve()
    if not sdk.is_absolute() or not sdk.is_dir():
        raise ValueError("Darwin SDK did not resolve to an existing directory")
    return sdk


def driver_environment(environment):
    return {key: value for key, value in environment.items()
            if key != "CCC_OVERRIDE_OPTIONS" and not key.startswith("CLANG_CONFIG_FILE_")}


def validate_arguments(argv):
    for arg in argv:
        parts = arg[4:].split(',') if arg.startswith('-Wl,') else [arg]
        for index, part in enumerate(parts):
            # ld64 interprets these operands as dyld runtime paths, not response
            # files. Accept them only in their linker-option operand position.
            dyld_path = (index > 0 and parts[index - 1] in {"-rpath", "-install_name"}
                         and any(part == token or part.startswith(token + "/")
                                 for token in ("@loader_path", "@executable_path", "@rpath")))
            if ((part.startswith("@") and not dyld_path) or
                    part.startswith(("--ld-path=", "-fuse-ld=", "--config")) or
                    part in {"--ld-path", "-fuse-ld", "-filelist", "--no-default-config"}):
                raise ValueError('opaque response or competing linker selection in Darwin capture')


def capture_proxy(directory, compiler_driver, linker, capture):
    directory.mkdir()
    proxy = directory / 'clang'
    helper = Path(__file__).resolve()
    proxy.write_text('#!' + sys.executable + '\nimport os\nos.execv(' + repr(sys.executable) +
                     ', ' + repr([sys.executable, str(helper), '--capture', str(compiler_driver),
                                  str(linker), str(capture)]) + ' + __import__("sys").argv[1:])\n')
    proxy.chmod(0o755)
    return proxy


def capture_link(driver, linker, capture, argv):
    validate_arguments(argv)
    # Pin the actual Mach-O linker selected by clang, including discovery probes.
    command = [driver, '--ld-path=' + linker, '--no-default-config', *argv]
    if '-o' not in argv or '-c' in argv:
        return subprocess.call(command, env=driver_environment(os.environ))
    output = Path(argv[argv.index('-o') + 1]).resolve()
    inputs = {str(Path(arg).resolve()): digest(arg) for arg in argv
              if not arg.startswith('-') and Path(arg).is_file()}
    record = {'driver': driver, 'driver_sha256': digest(driver),
              'linker': linker, 'linker_sha256': digest(linker),
              'cwd': os.getcwd(), 'argv': command[1:], 'inputs': inputs,
              'output': str(output)}
    code = subprocess.call(command, env=driver_environment(os.environ))
    if code == 0:
        record['output_sha256'] = digest(output)
        # Multiple hosted links are ambiguous and must fail closed.
        with Path(capture).open('x') as stream:
            json.dump(record, stream, sort_keys=True)
    return code


def verify_capture(capture, captured_output, driver, linker):
    record = json.loads(Path(capture).read_text())
    if (record['driver'] != str(driver) or record['driver_sha256'] != digest(driver) or
            record['linker'] != str(linker) or record['linker_sha256'] != digest(linker) or
            record['output'] != str(captured_output) or record['output_sha256'] != digest(captured_output)):
        raise ValueError('Darwin natural link driver/linker/output identity mismatch')
    root = Path(record['cwd'])
    for name, sha in record['inputs'].items():
        if digest(name) != sha:
            raise ValueError('Darwin captured link input changed: ' + name)
    if record['argv'][:2] != ['--ld-path=' + str(linker), '--no-default-config']:
        raise ValueError('Darwin capture lacks pinned linker argument')
    validate_arguments(record['argv'][2:])
    return record, root


def replay_inputs(capture, captured_output, driver, linker, main, provider, output):
    record, root = verify_capture(capture, captured_output, driver, linker)
    wanted = {digest(main): str(main), digest(provider): str(provider)}
    if len(wanted) != 2:
        raise ValueError('Darwin main/provider identity collision')
    found = set()
    argv = []
    for arg in record['argv']:
        path = str((root / arg).resolve())
        sha = record['inputs'].get(path)
        if sha in wanted:
            if sha in found:
                raise ValueError('ambiguous duplicate Darwin main/provider input')
            found.add(sha)
            arg = wanted[sha]
        argv.append(arg)
    if found != set(wanted):
        raise ValueError('Darwin capture did not consume exact emitted main/provider bytes')
    argv.extend(['-o', str(output)])
    return [str(driver), *argv], root


if __name__ == '__main__':
    if len(sys.argv) < 6 or sys.argv[1] != '--capture':
        raise SystemExit('private capture helper requires driver, linker, capture, arguments')
    raise SystemExit(capture_link(*sys.argv[2:5], sys.argv[5:]))
