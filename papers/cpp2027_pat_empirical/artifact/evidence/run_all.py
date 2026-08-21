#!/usr/bin/env python3
"""run_all.py — 一键复现全部训练任务 (E12 五组 × 3 seeds)

用法:
    python3 experiments/run_all.py
    # 输出 → results/run_all_out.txt (训练 acc + OOD 逐 seed)

自包含: 全部依赖在本包 runtime/ 内 (tokenizer/train/synth/archive/lab),
仅需 python3 + torch (见 environment.md)。
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RUNTIME = os.path.join(ROOT, "runtime")
LAB = os.path.join(RUNTIME, "lab")
OUT = os.path.join(ROOT, "results", "run_all_out.txt")


def find_python():
    """选择 python 解释器: PYTHON 环境变量 > 真实 python 的 sys.executable > venv 回退。

    某些 shell 环境将 python3 劫持为应用启动器 (非解释器), 必须显式规避。
    """
    exe = os.environ.get("PYTHON", "")
    if exe and os.path.exists(exe):
        return exe
    base = os.path.basename(sys.executable).lower()
    if "python" in base and "appimage" not in base:
        return sys.executable
    for c in (
        os.path.join(os.path.dirname(ROOT), ".venv", "bin", "python3"),
        os.path.join(ROOT, ".venv", "bin", "python3"),
        "/usr/bin/python3",
    ):
        if os.path.exists(c):
            return c
    return sys.executable


PY = find_python()


def find_site_packages(py):
    """探测 venv site-packages (PYTHONPATH 式 venv: 需显式加入)."""
    venv_root = os.path.dirname(os.path.dirname(py))
    lib = os.path.join(venv_root, "lib")
    if os.path.isdir(lib):
        for d in os.listdir(lib):
            sp = os.path.join(lib, d, "site-packages")
            if os.path.isdir(sp):
                return sp
    return None


env = dict(os.environ)
paths = [RUNTIME, LAB]
sp = find_site_packages(PY)
if sp:
    paths.insert(0, sp)
if env.get("PYTHONPATH"):
    paths.append(env["PYTHONPATH"])
env["PYTHONPATH"] = os.pathsep.join(paths)
env["PYTHONUNBUFFERED"] = "1"

cmd = [PY, os.path.join(HERE, "succ_matrix_exp.py")]
print(f"python: {PY}")
print(f"运行: {' '.join(cmd)}")
print(f"输出: {OUT}")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w") as f:
    r = subprocess.run(cmd, env=env, stdout=f, stderr=subprocess.STDOUT)
print(f"退出码: {r.returncode}")
sys.exit(r.returncode)
