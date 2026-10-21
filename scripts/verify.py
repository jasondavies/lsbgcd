#!/usr/bin/env python3
"""Build and verify the project with the locally installed Lean toolchain."""
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build" / "local"


def find_lake():
    lake = shutil.which("lake")
    if lake:
        return lake
    elan_home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    lake = elan_home / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if lake.is_file():
        return str(lake)
    raise RuntimeError("Lake is not installed. Install elan as described in README.md.")


def call(lake, name, *args, default_env=None):
    report = OUT / (name + ".log")
    env = os.environ.copy()
    env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
    for key, value in (default_env or {}).items():
        env.setdefault(key, value)
    print(f"Running {name}…", flush=True)
    with report.open("w") as log:
        proc = subprocess.run(
            [lake, *args], cwd=ROOT, env=env,
            stdout=log, stderr=subprocess.STDOUT,
        )
    if proc.returncode:
        print(report.read_text(), file=sys.stderr)
        raise RuntimeError(f"{name} failed (exit {proc.returncode}); see {report}")
    print(f"{name}: passed; log: {report}", flush=True)


def main():
    lake = find_lake()
    OUT.mkdir(parents=True, exist_ok=True)
    call(lake, "build", "build")
    # Each leanchecker thread holds about 7 GB, so replay on one thread unless
    # LEAN_NUM_THREADS is already set.
    call(lake, "kernel", "env", "leanchecker", "--verbose", "Lsbgcd",
         default_env={"LEAN_NUM_THREADS": "1"})
    call(lake, "axioms", "env", "lean", "scripts/Audit.lean")
    print("Local Lean verification passed.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
