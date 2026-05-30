#!/usr/bin/env python3
"""Headless worktree smoke tests for src/app/nvim_plugin."""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PLUGIN = ROOT / "src" / "app" / "nvim_plugin"


def run_nvim(name, lua_source, extra_args=None):
    extra_args = extra_args or []
    with tempfile.TemporaryDirectory(prefix="simple-nvim-") as tmp:
        tmp_path = Path(tmp)
        script = tmp_path / "case.lua"
        script.write_text(lua_source, encoding="utf-8")
        env = os.environ.copy()
        env.update(
            {
                "HOME": str(tmp_path / "home"),
                "XDG_CONFIG_HOME": str(tmp_path / "config"),
                "XDG_DATA_HOME": str(tmp_path / "data"),
                "XDG_STATE_HOME": str(tmp_path / "state"),
                "XDG_CACHE_HOME": str(tmp_path / "cache"),
            }
        )
        for key in ("home", "config", "data", "state", "cache"):
            (tmp_path / key).mkdir(parents=True, exist_ok=True)

        cmd = [
            "nvim",
            "--headless",
            "-u",
            "NONE",
            "-i",
            "NONE",
            *extra_args,
            "-c",
            f"luafile {script}",
            "-c",
            "qa!",
        ]
        result = subprocess.run(
            cmd,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
        )
        if result.returncode != 0:
            raise AssertionError(
                f"{name} failed with exit {result.returncode}\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
            )


def plugin_bootstrap(body):
    return f"""
vim.opt.runtimepath:prepend({PLUGIN.as_posix()!r})
vim.cmd("runtime plugin/simple.lua")
local function assert_eq(actual, expected, label)
  if actual ~= expected then
    error(label .. ": expected " .. vim.inspect(expected) .. ", got " .. vim.inspect(actual))
  end
end
local function assert_true(value, label)
  if not value then
    error(label)
  end
end
{body}
"""


def main():
    if not PLUGIN.is_dir():
        raise AssertionError(f"missing plugin directory: {PLUGIN}")

    run_nvim(
        "lua syntax",
        plugin_bootstrap(
            r"""
for _, path in ipairs(vim.fn.glob("src/app/nvim_plugin/**/*.lua", true, true)) do
  local fn, err = loadfile(path)
  assert_true(fn ~= nil, path .. ": " .. tostring(err))
end
"""
        ),
    )

    run_nvim(
        "filetype detection and setup",
        plugin_bootstrap(
            r"""
vim.cmd("edit smoke.spl")
assert_eq(vim.bo.filetype, "simple", "spl filetype")
require("simple").setup({
  lsp = { enabled = false },
  math = { enabled = false },
  commands = { enabled = true },
  treesitter = { ensure_installed = false },
})
assert_true(vim.fn.exists(":SimpleTest") == 2, "SimpleTest command missing")
assert_true(vim.fn.exists(":SimpleLspRestart") == 2, "SimpleLspRestart command missing")
"""
        ),
    )

    run_nvim(
        "worktree lsp command discovery",
        plugin_bootstrap(
            r"""
local lsp = require("simple.lsp")
local cmd, err = lsp._find_server_cmd(vim.fn.getcwd(), {})
assert_true(cmd ~= nil, err or "missing command")
assert_true(cmd[1]:match("/bin/simple$") ~= nil, "expected worktree bin/simple, got " .. vim.inspect(cmd))
assert_eq(cmd[2], "lsp", "lsp subcommand")

local bad, bad_err = lsp._find_server_cmd(vim.fn.getcwd(), { cmd = { "", "lsp" } })
assert_eq(bad, nil, "invalid cmd result")
assert_true(type(bad_err) == "string" and bad_err:match("non%-empty") ~= nil, "invalid cmd error")
"""
        ),
    )

    run_nvim(
        "treesitter query discovery",
        plugin_bootstrap(
            r"""
local ts = require("simple.treesitter")
ts.setup({})
local query_path = ts.get_query_path()
assert_true(query_path ~= nil, "query path not found")
assert_true(query_path:match("src/compiler/10%.frontend/parser/treesitter/queries$") ~= nil, query_path)
assert_true(vim.fn.filereadable(query_path .. "/highlights.scm") == 1, "missing highlights query")
"""
        ),
    )

    run_nvim(
        "ftplugin keyword policy",
        plugin_bootstrap(
            r"""
vim.cmd("edit smoke.spl")
vim.bo.filetype = "simple"
vim.cmd("runtime ftplugin/simple.lua")
assert_true(vim.bo.commentstring == "# %s", "commentstring not configured")
assert_true(vim.bo.iskeyword:find("!", 1, true) ~= nil, "! should be keyword")
assert_true(vim.bo.iskeyword:find("?", 1, true) == nil, "? must remain an operator")
"""
        ),
    )

    run_nvim(
        "command shell escaping",
        plugin_bootstrap(
            r"""
require("simple").setup({
  lsp = { enabled = false },
  math = { enabled = false },
  commands = { enabled = true, test_cmd = { "bin/simple", "test" } },
  treesitter = { ensure_installed = false },
})
local commands = require("simple.commands")
local joined = commands._shell_join({ "bin/simple", "test", "a file; touch /tmp/simple_nvim_bad" })
assert_true(joined:match("touch") ~= nil, "test arg missing")
assert_true(joined:match("'a file; touch /tmp/simple_nvim_bad'") ~= nil, "dangerous arg was not shell-quoted: " .. joined)
"""
        ),
    )

    run_nvim(
        "lsp worktree client starts",
        plugin_bootstrap(
            r"""
vim.cmd("edit smoke.spl")
vim.bo.filetype = "simple"
local simple = require("simple")
simple.setup({
  math = { enabled = false },
  commands = { enabled = false },
  treesitter = { ensure_installed = false },
})
local id = require("simple.lsp")._start_for_buffer(0, simple.config.lsp)
local client = vim.lsp.get_client_by_id(id)
assert_true(client ~= nil, "LSP client did not start")
assert_eq(client.name, "simple_ls", "LSP client name")
client:stop()
"""
        ),
    )

    print("STATUS: PASS nvim_plugin_smoke")


if __name__ == "__main__":
    if shutil.which("nvim") is None:
        print("SKIP: nvim not found")
        raise SystemExit(0)
    try:
        main()
    except Exception as exc:
        print(f"STATUS: FAIL nvim_plugin_smoke: {exc}", file=sys.stderr)
        raise
