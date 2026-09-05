#!/usr/bin/env node
import { appendFileSync, chmodSync, existsSync, lstatSync, mkdirSync, readlinkSync, readdirSync, readFileSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { dirname, isAbsolute, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

await runCli();
