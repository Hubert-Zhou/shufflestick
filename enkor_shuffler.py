# -*- coding: utf-8 -*-
"""
ShuffleStick · U 盘歌单乱序助手

给「不支持随机播放」的设备用的歌单乱序工具：车载车机、老式 MP3、蓝牙音箱、
骨传导耳机、广场舞音响、电视 USB 播放等，只要它把 U 盘当 FAT32 目录遍历就能用。

背景：这类播放模块通常由廉价 FAT32 固件直接遍历目录，不同固件可能按
【文件名字典序】/【FAT 目录项(拷贝)顺序】/【修改时间】/【物理簇号】之一播放。
网上流行的「改名加 01_ 序号」教程只对第一种有效。本工具提供只读诊断帮你判定，
并提供三种重排策略覆盖不同固件。

三种模式：
  极速重排  —— 同盘 move 进暂存目录再按随机序 move 回来。零字节数据搬运，秒级，
               不需要电脑备份。FAT 目录项顺序跟随 move 顺序（--fat-probe 可复验）。
  清盘重写  —— 备份到电脑 → 删除音频 → 按随机顺序重新写入（连物理簇一起换）。
               要搬两遍数据，耗时取决于你的 U 盘吞吐，慢盘可能需要数十分钟。
  仅重命名  —— 只改编号前缀 + 修改时间，不删除文件（对按拷贝顺序读的固件无效）。

所有写操作都需手动点「执行」并二次确认；设备白名单之外的 U 盘一律拒绝写入；
插盘只提醒、绝不自动动手。每次操作都会留还原清单。

免费、开源（MIT）、不联网、不上传、无广告、无捆绑。
"""
from __future__ import annotations

import ctypes
import json
import os
import queue
import random
import re
import shutil
import stat
import sys
import threading
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path

try:
    import tkinter as tk
    from tkinter import ttk, messagebox, filedialog
except ModuleNotFoundError:            # 允许在无 GUI 的解释器上跑 --selftest
    tk = ttk = messagebox = filedialog = None

APP_NAME = "U 盘歌单乱序助手"
APP_ID = "ShuffleStick"
APP_VERSION = "0.9.0"
APP_TITLE = f"{APP_NAME} v{APP_VERSION} · 免费开源"
LICENSE_NAME = "MIT"
SOURCE_URL = "https://github.com/Hubert-Zhou/shufflestick"
SOURCE_URL_MIRROR = ""            # 只用一个仓库时留空
DONATE_SLOGAN = "愿下一首也刚好，就当见过面。"   # 赞赏码上方的一句话
ASSUMED_MBPS = 1.0               # 仅用于「保守估算」提示，实际吞吐因设备而异

# 源码版：数据放脚本旁；PyInstaller 版：__file__ 指向临时解压目录 _MEIPASS，
# 必须锚定到 exe 所在目录，否则配置、日志、备份会在退出后被清理掉。
BASE = (Path(sys.executable).resolve().parent if getattr(sys, "frozen", False)
        else Path(__file__).resolve().parent)
DATA = BASE / "shuffler_data"
BACKUP_ROOT = DATA / "backup"
LOG_ROOT = DATA / "logs"
MANIFEST = DATA / "last_manifest.json"
ASSETS = BASE / "assets"
DONATE_IMAGE = ASSETS / "donate_wechat.png"

AUDIO_EXTS = {".mp3", ".flac", ".wav", ".aac", ".m4a", ".ape",
              ".ogg", ".wma", ".mp2", ".aif", ".aiff", ".alac"}
PREFIX_RE = re.compile(r"^\s*\d{1,4}\s*[._\-—]\s*")
BAD_CHARS_RE = re.compile(r'[\\/:*?"<>|\r\n]')
DRIVE_REMOVABLE = 2
DRIVE_FIXED = 3
FILE_ATTRIBUTE_READONLY = 0x1
SWAP_DIR = "_SHUF_SWAP_"       # 极速重排用的临时目录（同盘，仅短名，兼容 FAT32）
COPY_BUF = 4 * 1024 * 1024     # 4 MB 大块 IO，减少慢速 USB 设备的固定延迟开销

for d in (DATA, BACKUP_ROOT, LOG_ROOT):
    d.mkdir(parents=True, exist_ok=True)


def log(msg: str) -> None:
    line = f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}"
    try:
        with (LOG_ROOT / f"{datetime.now():%Y%m%d}.log").open("a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass
    # PyInstaller --windowed 下 sys.stdout 为 None，print 会抛错；日志写文件才是主路径
    try:
        if sys.stdout is not None:
            print(line)
    except Exception:
        pass


# --------------------------------------------------------------------------- 数据模型

@dataclass
class Track:
    orig_name: str
    size: int
    mtime: float
    readonly: bool
    ext: str
    dir_index: int          # os.scandir 顺序 ≈ FAT 目录项顺序 ≈ 拷贝顺序

    @property
    def short(self) -> str:
        return self.orig_name if len(self.orig_name) <= 46 else self.orig_name[:43] + "..."


def drive_type(letter: str) -> int:
    try:
        return ctypes.windll.kernel32.GetDriveTypeW(ctypes.c_wchar_p(f"{letter}:\\"))
    except Exception:
        return 0


def list_drives() -> list[str]:
    """列出所有非系统盘；可移动盘优先。"""
    removable, fixed = [], []
    for c in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
        root = f"{c}:\\"
        if not os.path.isdir(root):
            continue
        t = drive_type(c)
        if t == DRIVE_REMOVABLE:
            removable.append(root)
        elif t == DRIVE_FIXED and c not in ("C",):
            fixed.append(root)
    return removable + fixed


def preferred_drive(drives: list[str]) -> str:
    """默认目标：第一个可移动盘；没有可移动盘时留空，避免把固定盘误当成 U 盘。

    注意：不禁止用户手动在下拉框里选固定盘（safe_target_root 允许 DRIVE_FIXED），
    这里只负责「自动默认值」这一件事。
    """
    for d in drives:
        if d and drive_type(d[0]) == DRIVE_REMOVABLE:
            return d
    return ""


def volume_info(root: str) -> str:
    """返回 文件系统 / 剩余空间 描述。"""
    try:
        fs_buf = ctypes.create_unicode_buffer(64)
        ctypes.windll.kernel32.GetVolumeInformationW(
            ctypes.c_wchar_p(root), None, 0, None, None, None, fs_buf, 64)
        fs = fs_buf.value or "?"
        free = shutil.disk_usage(root).free
        kind = "可移动" if drive_type(root[0]) == DRIVE_REMOVABLE else "固定磁盘"
        return f"{fs} · {kind} · 可用 {free / 1024**3:.1f} GB"
    except Exception as exc:
        return f"信息读取失败：{exc}"


def volume_serial(root: str) -> str:
    """卷序列号：把自动洗牌绑定到这一块 U 盘，防止别的盘占用同一盘符被误洗。"""
    try:
        s = ctypes.c_ulong(0)
        ok = ctypes.windll.kernel32.GetVolumeInformationW(
            ctypes.c_wchar_p(root), None, 0, ctypes.byref(s), None, None, None, 0)
        return f"{s.value:08X}" if ok else ""
    except Exception:
        return ""


def rotate_backups(keep: int = 3) -> None:
    """自动洗牌会反复备份，只留最近 keep 份；当前还原清单指向的那份永不清理。"""
    protected = ""
    try:
        if MANIFEST.is_file():
            protected = json.loads(MANIFEST.read_text(encoding="utf-8")).get("backup_dir", "")
    except Exception:
        pass
    try:
        dirs = sorted((d for d in BACKUP_ROOT.iterdir() if d.is_dir()),
                      key=lambda d: d.name, reverse=True)
    except OSError:
        return
    kept = 0
    for d in dirs:
        if str(d) == protected:
            continue
        kept += 1
        if kept <= keep:
            continue
        for f in d.iterdir():                 # 只清理本程序自建的备份目录
            try:
                f.unlink()
            except OSError:
                pass
        try:
            d.rmdir()
            log(f"清理旧备份：{d}")
        except OSError:
            pass


def safe_target_root(root: str) -> None:
    """写操作前的硬护栏，防止误操作系统盘或任意目录。"""
    p = Path(root)
    if not p.exists() or p.anchor != str(p):
        raise RuntimeError("目标必须是盘符根目录（例如 E:\\）")
    letter = p.drive.rstrip(":\\").upper()
    if letter in ("C", ""):
        raise RuntimeError("拒绝操作系统盘 C:")
    if drive_type(letter) not in (DRIVE_REMOVABLE, DRIVE_FIXED):
        raise RuntimeError("目标不是本地磁盘")


def scan(root: str, recursive: bool = False, guard: bool = True) -> list[Track]:
    """只读扫描。os.scandir 的顺序即目录枚举顺序，用来推断拷贝顺序。

    guard=True 时沿用写操作的「必须是盘符根目录」护栏；
    只读诊断传 guard=False，允许扫描任意目录而完全不承担写风险。
    """
    if guard:
        safe_target_root(root)
    out: list[Track] = []
    idx = 0
    def walk(folder: str):
        nonlocal idx
        try:
            entries = list(os.scandir(folder))
        except OSError as exc:
            log(f"跳过目录 {folder}: {exc}")
            return
        for e in entries:
            try:
                if e.is_dir(follow_symlinks=False):
                    if recursive and not e.name.lower().startswith(("system volume", "$recycle")):
                        walk(e.path)
                    continue
                ext = Path(e.name).suffix.lower()
                if ext not in AUDIO_EXTS:
                    continue
                st = e.stat()
                attrs = getattr(st, "st_file_attributes", 0)
                out.append(Track(
                    orig_name=e.name,
                    size=st.st_size,
                    mtime=st.st_mtime,
                    readonly=bool(attrs & FILE_ATTRIBUTE_READONLY),
                    ext=ext,
                    dir_index=idx,
                ))
                idx += 1
            except OSError as exc:
                log(f"跳过 {e.name}: {exc}")
    walk(root)
    return out


def clean_name(name: str) -> str:
    name = BAD_CHARS_RE.sub("_", PREFIX_RE.sub("", name)).strip()
    return (name[:180] or "track")


def build_plan(order: list[Track], safe_names: bool) -> list[dict]:
    """生成随机序列的写入计划：编号前缀 / 目标名 / 递增时间戳，三者一致。"""
    # FAT32 时间戳精度为 2 秒，步长取 2 秒保证顺序可分辨
    base = time.time() - (len(order) + 2) * 2
    plan = []
    for i, t in enumerate(order, start=1):
        dst = f"{i:03d}{t.ext.lower()}" if safe_names else f"{i:03d}_{clean_name(t.orig_name)}"
        plan.append({
            "seq": i,
            "src": t.orig_name,
            "dst": dst,
            "mtime": base + i * 2,
            "size": t.size,
        })
    return plan


def make_order(tracks: list[Track], seed: str = "") -> list[Track]:
    """真随机洗牌；保证和原顺序有足够差异，避免"洗了个寂寞"。"""
    if len(tracks) < 2:
        raise RuntimeError("音频文件少于 2 首，无需洗牌")
    rnd = random.Random(seed) if seed.strip() else random.SystemRandom()
    best = None
    best_score = -1
    for _ in range(12):
        candidate = list(tracks)
        rnd.shuffle(candidate)
        score = sum(1 for a, b in zip(tracks, candidate) if a.orig_name != b.orig_name)
        if score > best_score:
            best, best_score = candidate, score
        if score >= max(2, int(len(tracks) * 0.8)):
            break
    return best


def clear_readonly(path: Path) -> None:
    try:
        os.chmod(path, stat.S_IWRITE | stat.S_IREAD)
    except OSError:
        try:
            ctypes.windll.kernel32.SetFileAttributesW(
                ctypes.c_wchar_p(str(path)), 0x80)  # FILE_ATTRIBUTE_NORMAL
        except Exception:
            pass


def set_readonly(path: Path) -> None:
    try:
        ctypes.windll.kernel32.SetFileAttributesW(
            ctypes.c_wchar_p(str(path)), FILE_ATTRIBUTE_READONLY)
    except Exception:
        pass


# --------------------------------------------------------------------------- IO 辅助

def fast_copy(src: Path, dst: Path) -> int:
    """大块顺序拷贝。慢速 USB 设备对每次小块提交有固定延迟，4 MB 块可明显减少提交次数。"""
    with open(src, "rb", buffering=COPY_BUF) as f, open(dst, "wb", buffering=COPY_BUF) as g:
        shutil.copyfileobj(f, g, length=COPY_BUF)
    return dst.stat().st_size


def pace(t0: float, done_bytes: int, total_bytes: int, prefix: str) -> str:
    """进度文字补上实时速度与预计剩余时间，长任务不再盲等。"""
    el = time.time() - t0
    if el < 1 or done_bytes <= 0:
        return prefix
    rate = done_bytes / el
    left = max(0, total_bytes - done_bytes)
    eta = int(left / max(rate, 1))
    mm, ss = divmod(eta, 60)
    return f"{prefix} · {rate / 1024**2:.1f} MB/s · 剩余约 {mm}分{ss:02d}秒"


class keep_awake:
    """长任务期间阻止系统进入睡眠/休眠（锁屏本身不中断进程，合盖与空闲会）。"""
    ES_CONTINUOUS, ES_SYSTEM_REQUIRED = 0x80000000, 0x00000001

    def __enter__(self):
        try:
            ctypes.windll.kernel32.SetThreadExecutionState(
                self.ES_CONTINUOUS | self.ES_SYSTEM_REQUIRED)
        except Exception:
            pass
        return self

    def __exit__(self, *exc):
        try:
            ctypes.windll.kernel32.SetThreadExecutionState(self.ES_CONTINUOUS)
        except Exception:
            pass
        return False


def recover_swap(rootp: Path, progress) -> int:
    """上次极速重排中断时，把暂存目录里的文件安全移回根目录（零拷贝，不丢数据）。"""
    swap = rootp / SWAP_DIR
    if not swap.is_dir():
        return 0
    n = 0
    for p in list(swap.iterdir()):
        if not p.is_file():
            continue
        dst = rootp / p.name
        if dst.exists():
            dst = rootp / f"_recovered_{n:03d}_{p.name}"
        clear_readonly(p)
        p.rename(dst)
        n += 1
    try:
        swap.rmdir()
    except OSError:
        pass
    if n:
        log(f"恢复上次中断的暂存文件：{n} 个（来自 {swap}）")
        progress(0, 100, f"已恢复上次中断的 {n} 个文件")
    return n


# --------------------------------------------------------------------------- 执行

def apply_fast(root: str, plan: list[dict], tracks: list[Track],
               safe_names: bool, progress) -> None:
    """
    零拷贝重排：同盘 move 只改 FAT 目录项，不搬一字节数据、不需要电脑备份。

    实测（--fat-probe）：全量移出后，目录项顺序完全跟随「移回顺序」。
    因此把文件按随机序列移回根目录 == 改变设备的拷贝/目录项播放顺序。
    """
    safe_target_root(root)
    rootp = Path(root)
    swap = rootp / SWAP_DIR
    recover_swap(rootp, progress)                  # 幂等：无残留时立即返回
    if swap.exists():
        raise RuntimeError(f"暂存目录 {SWAP_DIR} 无法清理，请检查 U 盘后重试")
    n = len(plan)
    with keep_awake():
        swap.mkdir()
        # 1. 全部移入暂存：同分区 rename 是元数据操作，不复制数据
        for i, t in enumerate(tracks):
            src = rootp / t.orig_name
            if not src.is_file():
                raise RuntimeError(f"文件不见了：{t.orig_name}")
            clear_readonly(src)
            src.rename(swap / t.orig_name)
            progress(i + 1, n * 2, f"整理目录项 {i + 1}/{n}（零拷贝）")
        # 2. 按随机序列移回根目录，顺带改编号前缀和时间戳
        try:
            for i, item in enumerate(plan):
                src = swap / item["src"]
                dst = rootp / item["dst"]
                if dst.exists():
                    raise RuntimeError(f"目标名冲突：{item['dst']}")
                clear_readonly(src)
                src.rename(dst)
                os.utime(dst, (item["mtime"], item["mtime"]))
                progress(n + i + 1, n * 2, f"按新顺序排列 {i + 1}/{n}（零拷贝）")
        except Exception:
            recover_swap(rootp, progress)          # 保证任何失败都不丢数据
            raise
        if any(p.is_file() for p in swap.iterdir()):
            recover_swap(rootp, progress)
            raise RuntimeError("暂存目录仍有文件，已把文件全部移回根目录")
        swap.rmdir()

    # 3. 回读校验：目录项顺序是否真的等于随机序列（纯元数据读取，零成本）
    actual = [x.orig_name for x in scan(root)]
    verified = actual == [p["dst"] for p in plan]
    if verified:
        log("目录项顺序校验通过：与随机序列完全一致")
    else:
        log(f"警告：目录项顺序校验未通过，实际前 3 = {actual[:3]}")

    manifest = {
        "created": datetime.now().isoformat(timespec="seconds"),
        "root": root,
        "mode": "fast",
        "safe_names": safe_names,
        "backup_dir": "",
        "verified": verified,
        "tracks": [asdict(t) for t in tracks],
        "plan": plan,
    }
    MANIFEST.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    progress(100, 100, "完成")
    log(f"极速重排完成：{root} 共 {n} 首 · 零字节数据搬运")


def apply_rename(root: str, plan: list[dict], progress) -> None:
    """仅重命名 + 重设时间戳。不删除任何文件。"""
    safe_target_root(root)
    rootp = Path(root)
    n = len(plan)
    # 阶段 1：全部改成唯一临时名，规避中间名冲突
    tmps = []
    for i, item in enumerate(plan):
        src = rootp / item["src"]
        if not src.is_file():
            raise RuntimeError(f"文件不见了：{item['src']}")
        tmp = rootp / f"__swp{i:04d}__.tmp"
        clear_readonly(src)
        src.rename(tmp)
        tmps.append(tmp)
        progress(i + 1, n * 2, f"暂存 {i + 1}/{n}")
    # 阶段 2：改成最终名 + 时间戳
    for i, (tmp, item) in enumerate(zip(tmps, plan)):
        dst = rootp / item["dst"]
        if dst.exists():
            raise RuntimeError(f"目标名冲突：{item['dst']}")
        tmp.rename(dst)
        t = item["mtime"]
        os.utime(dst, (t, t))
        progress(n + i + 1, n * 2, f"写入 {i + 1}/{n}")
    log(f"仅重命名完成：{root} 共 {n} 首")


def apply_rewrite(root: str, plan: list[dict], tracks: list[Track], safe_names: bool,
                  progress) -> None:
    """清盘重写：备份 → 校验 → 删除 → 按随机顺序写回（改变 FAT 目录项顺序）。"""
    safe_target_root(root)
    rootp = Path(root)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup = BACKUP_ROOT / stamp
    backup.mkdir(parents=True, exist_ok=True)

    # 1. 全量备份（含原始顺序元数据）
    total_bytes = sum(t.size for t in tracks)
    workload = total_bytes * 2          # 备份读一遍 + 写回写一遍
    t0, done_bytes = time.time(), 0
    progress(0, 100, "备份到电脑…")
    for i, t in enumerate(tracks):
        fast_copy(rootp / t.orig_name, backup / t.orig_name)
        done_bytes += t.size
        progress(1 + int(29 * (i + 1) / len(tracks)), 100,
                 pace(t0, done_bytes, workload, f"备份 {i + 1}/{len(tracks)}"))

    # 2. 校验备份：数量 + 每个文件大小
    for t in tracks:
        b = backup / t.orig_name
        if not b.is_file() or b.stat().st_size != t.size:
            raise RuntimeError(f"备份校验失败：{t.orig_name}（已中止，U 盘未改动）")
    progress(30, 100, "备份校验通过")

    # 3. 删除 U 盘上的音频文件（只删本次扫描到的白名单后缀，绝不递归删目录）
    for i, t in enumerate(tracks):
        p = rootp / t.orig_name
        if p.suffix.lower() not in AUDIO_EXTS:
            raise RuntimeError(f"拒绝删除非音频文件：{t.orig_name}")
        clear_readonly(p)
        p.unlink()
        progress(30 + int(20 * (i + 1) / len(tracks)), 100, f"清空 {i + 1}/{len(tracks)}")

    # 4. 按随机序列逐个写回 —— 目录项顺序 == 写入顺序 == 文件名序 == 时间戳序
    for i, item in enumerate(plan):
        src = backup / item["src"]
        dst = rootp / item["dst"]
        fast_copy(src, dst)
        done_bytes += item["size"]
        t = item["mtime"]
        os.utime(dst, (t, t))
        progress(50 + int(45 * (i + 1) / len(plan)), 100,
                 pace(t0, done_bytes, workload, f"按新顺序写入 {i + 1}/{len(plan)}"))

    # 5. 落还原清单（只存电脑本地，U 盘上不留任何非音频文件）
    manifest = {
        "created": datetime.now().isoformat(timespec="seconds"),
        "root": root,
        "mode": "rewrite",
        "safe_names": safe_names,
        "backup_dir": str(backup),
        "tracks": [asdict(t) for t in tracks],
        "plan": plan,
    }
    MANIFEST.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    (backup / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    rotate_backups()
    progress(100, 100, "完成")
    log(f"清盘重写完成：{root} 共 {len(plan)} 首，备份 {backup}")


def apply_all(root: str, mode: str, plan: list[dict], tracks: list[Track],
              safe_names: bool, progress) -> None:
    if mode == "fast":
        apply_fast(root, plan, tracks, safe_names, progress)
        return
    if mode == "rename":
        apply_rename(root, plan, progress)
        manifest = {
            "created": datetime.now().isoformat(timespec="seconds"),
            "root": root,
            "mode": "rename",
            "safe_names": safe_names,
            "backup_dir": "",
            "tracks": [asdict(t) for t in tracks],
            "plan": plan,
        }
        MANIFEST.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    elif mode == "rewrite":
        apply_rewrite(root, plan, tracks, safe_names, progress)
    else:
        raise RuntimeError("未知模式")


def restore_fast(rootp: Path, m: dict, tracks: list[Track],
                 plan: list[dict], progress) -> str:
    """极速重排的还原：同样零拷贝，把目录项和名字按原顺序排回去。"""
    swap = rootp / SWAP_DIR
    by_src = {p["src"]: p["dst"] for p in plan}      # 原名 -> 洗牌后的名字
    ordered = sorted(tracks, key=lambda t: t.dir_index)
    cur = [(t, by_src.get(t.orig_name, t.orig_name)) for t in ordered]

    progress(0, 100, "检查当前文件…")
    for t, name in cur:
        if not (rootp / name).is_file():
            raise RuntimeError(f"还原中止：找不到 {name}（U 盘文件可能被手工改过）")
    recover_swap(rootp, progress)
    if swap.exists():
        raise RuntimeError(f"暂存目录 {SWAP_DIR} 无法清理，还原中止")
    swap.mkdir()

    for i, (t, name) in enumerate(cur):
        clear_readonly(rootp / name)
        (rootp / name).rename(swap / f"{i:04d}.tmp")
        progress(int(45 * (i + 1) / len(cur)), 100, f"整理目录项 {i + 1}/{len(cur)}")
    try:
        for i, (t, name) in enumerate(cur):
            dst = rootp / t.orig_name
            if dst.exists():
                raise RuntimeError(f"还原冲突：{t.orig_name} 已存在")
            (swap / f"{i:04d}.tmp").rename(dst)
            os.utime(dst, (t.mtime, t.mtime))
            if t.readonly:
                set_readonly(dst)
            progress(45 + int(50 * (i + 1) / len(cur)), 100, f"还原 {i + 1}/{len(cur)}")
    except Exception:
        recover_swap(rootp, progress)
        raise
    swap.rmdir()
    progress(100, 100, "还原完成")
    log(f"还原完成：{rootp} 模式 fast（零拷贝）")
    return f"已还原 {len(cur)} 首（极速重排 · 零拷贝）"


def restore(progress) -> str:
    """一键还原到上一次操作之前的文件名、目录顺序与时间戳。"""
    if not MANIFEST.is_file():
        raise RuntimeError("没有找到还原清单，说明还没执行过洗牌")
    m = json.loads(MANIFEST.read_text(encoding="utf-8"))
    root = m["root"]
    rootp = Path(root)
    safe_target_root(root)
    tracks = [Track(**x) for x in m["tracks"]]
    plan = m["plan"]
    mode = m["mode"]
    if mode == "fast":
        return restore_fast(rootp, m, tracks, plan, progress)

    # 当前 U 盘上的文件 → 先改名成临时名（rewrite 模式下当前名 = plan 的 dst）
    cur_names = [p["dst"] if mode == "rewrite" else p["dst"] for p in plan]
    if mode == "rename":
        # rename 模式的目标名就是 plan.dst，按 seq 对应
        cur_names = [p["dst"] for p in sorted(plan, key=lambda x: x["seq"])]

    progress(0, 100, "检查当前文件…")
    for name in cur_names:
        if not (rootp / name).is_file():
            raise RuntimeError(f"还原中止：找不到 {name}（U 盘文件可能被手工改过）")

    tmps = []
    for i, name in enumerate(cur_names):
        tmp = rootp / f"__rst{i:04d}__.tmp"
        clear_readonly(rootp / name)
        (rootp / name).rename(tmp)
        tmps.append(tmp)

    if mode == "rewrite":
        # 清盘重写模式：从备份按原目录顺序写回
        backup = Path(m["backup_dir"])
        ordered = sorted(tracks, key=lambda t: t.dir_index)
        for tmp in tmps:
            tmp.unlink()
        for i, t in enumerate(ordered):
            src = backup / t.orig_name
            if not src.is_file():
                raise RuntimeError(f"备份缺失：{t.orig_name}")
            shutil.copyfile(src, rootp / t.orig_name)
            os.utime(rootp / t.orig_name, (t.mtime, t.mtime))
            progress(int(95 * (i + 1) / len(ordered)), 100, f"还原 {i + 1}/{len(ordered)}")
        for t in ordered:
            if t.readonly:
                set_readonly(rootp / t.orig_name)
    else:
        # 仅重命名模式：按 seq 把临时名改回原名
        by_seq = {p["seq"]: p for p in plan}
        orig_by_src = {t.orig_name: t for t in tracks}
        # plan[i] 的 src 就是洗牌后位于第 seq 位的原文件名
        for i, tmp in enumerate(tmps):
            p = by_seq[i + 1]
            t = orig_by_src[p["src"]]
            dst = rootp / t.orig_name
            tmp.rename(dst)
            os.utime(dst, (t.mtime, t.mtime))
            if t.readonly:
                set_readonly(dst)
            progress(int(95 * (i + 1) / len(tmps)), 100, f"还原 {i + 1}/{len(tmps)}")

    log(f"还原完成：{root} 模式 {mode}")
    progress(100, 100, "还原完成")
    return f"已还原 {len(tracks)} 首（{mode}）"


# --------------------------------------------------------------------------- 随机拷贝：本地音频库 → 播放设备

CONFIG = DATA / "config.json"

DEFAULT_CONFIG = {
    "source_dir": "",            # 记住上一次指定的本地音频库目录
    "capacity_mb": 2048,         # 容量上限（MB）
    "recursive": True,           # 含子目录
    "avoid_repeat": True,        # 尽量避开上一批
    "last_batch": [],            # 上一批的 key（源库相对路径，小写）
    "device_whitelist": [],      # 已确认是播放设备的 U 盘指纹
    "remind_on_insert": False,   # 插盘仅提醒，绝不自动写盘
    "onboarded": False,          # 一次性引导是否已完成
    "shuffle_mode": "fast",      # 重排策略（原为主界面 radio，现收进设置）
    "safe_names": False,         # 是否改用 001.flac 安全短名
    "scan_recursive": False,     # 洗牌扫描是否含子目录
    "seed": "",                  # 随机种子
}


def load_config() -> dict:
    cfg = dict(DEFAULT_CONFIG)
    cfg["last_batch"] = []
    cfg["device_whitelist"] = []
    try:
        if CONFIG.is_file():
            saved = json.loads(CONFIG.read_text(encoding="utf-8"))
            if isinstance(saved, dict):
                for k in DEFAULT_CONFIG:
                    if k in saved:
                        cfg[k] = saved[k]
    except Exception as exc:
        log(f"配置读取失败，使用默认值：{exc}")
    return cfg


def save_config(cfg: dict) -> None:
    try:
        CONFIG.write_text(json.dumps(cfg, ensure_ascii=False, indent=2),
                          encoding="utf-8")
    except OSError as exc:
        log(f"配置保存失败：{exc}")


# -- 设备识别：只有显式绑定过的 U 盘才允许写 --------------------------------

def device_fingerprint(root: str) -> dict:
    """纯标准库读取卷指纹；不依赖 PowerShell，轮询里也能安全调用。"""
    fp = {"root": root, "serial": "", "label": "", "total": 0,
          "fs": "", "audio_count": 0, "model": ""}
    if not root or not os.path.isdir(root):
        return fp
    fp["serial"] = volume_serial(root)
    try:
        label_buf = ctypes.create_unicode_buffer(256)
        fs_buf = ctypes.create_unicode_buffer(64)
        ok = ctypes.windll.kernel32.GetVolumeInformationW(
            ctypes.c_wchar_p(root), label_buf, 256, None, None, None, fs_buf, 64)
        if ok:
            fp["label"], fp["fs"] = label_buf.value, fs_buf.value
    except Exception:
        pass
    try:
        fp["total"] = shutil.disk_usage(root).total
    except OSError:
        pass
    try:
        fp["audio_count"] = len(scan(root))
    except Exception:
        pass
    return fp


def usb_device_model(root: str) -> str:
    """一次性查询 USB 磁盘型号（只在「绑定」时调用）。失败返回空串，不影响主流程。"""
    letter = root[:1].upper()
    if not letter.isalpha():
        return ""
    script = ("try { $d = Get-Partition -DriveLetter '" + letter +
              "' -ErrorAction Stop | Get-Disk -ErrorAction Stop; "
              "$d.FriendlyName } catch { '' }")
    try:
        import subprocess
        out = subprocess.run(
            ["powershell", "-NoProfile", "-NonInteractive", "-Command", script],
            capture_output=True, text=True, timeout=8,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        lines = [x.strip() for x in (out.stdout or "").splitlines() if x.strip()]
        return lines[0] if lines and out.returncode == 0 else ""
    except Exception as exc:
        log(f"USB 型号查询跳过（不影响功能）：{exc}")
        return ""


def match_headset(fp: dict, cfg: dict) -> dict | None:
    """命中白名单才返回绑定记录。序列号必须一致，容量偏差 >10% 视为换盘。"""
    serial = str(fp.get("serial") or "").upper()
    if not serial:
        return None
    for item in cfg.get("device_whitelist", []):
        if str(item.get("serial") or "").upper() != serial:
            continue
        bound_total = int(item.get("total") or 0)
        now_total = int(fp.get("total") or 0)
        if bound_total and now_total and abs(bound_total - now_total) / bound_total > 0.10:
            continue
        return item
    return None


def is_headset(root: str, cfg: dict) -> bool:
    return match_headset(device_fingerprint(root), cfg) is not None


def bind_headset(root: str, cfg: dict, model: str = "") -> dict:
    fp = device_fingerprint(root)
    if not fp["serial"]:
        raise RuntimeError("读取不到卷序列号，无法绑定")
    fp["model"] = model or usb_device_model(root)
    rec = {
        "serial": fp["serial"], "label": fp["label"], "total": fp["total"],
        "fs": fp["fs"], "model": fp["model"] or "（型号未读到）",
        "audio_count": fp["audio_count"],
        "bound_at": datetime.now().isoformat(timespec="seconds"),
    }
    wl = [x for x in cfg.get("device_whitelist", [])
          if str(x.get("serial") or "").upper() != fp["serial"].upper()]
    wl.append(rec)
    cfg["device_whitelist"] = wl
    save_config(cfg)
    log(f"绑定播放设备：{root} / {fp['serial']} / {rec['model']}")
    return rec


# -- 本地音频库 --------------------------------------------------------------

@dataclass
class SourceTrack:
    path: str
    name: str
    size: int
    ext: str
    key: str                 # 源库相对路径（小写），用于「避开上一批」

    @property
    def mb(self) -> float:
        return self.size / 1024 / 1024


SKIP_DIRS = {"system volume information", "$recycle.bin", "recycler",
             ".git", "node_modules", "__pycache__", ".workbuddy"}


def scan_library(source: str, recursive: bool = True) -> list[SourceTrack]:
    """只读递归扫描本地音频库；返回按路径排序的稳定列表（随机在挑选阶段做）。"""
    root = Path(source)
    if not root.is_dir():
        raise RuntimeError(f"源目录不存在：{source}")
    out: list[SourceTrack] = []

    def walk(d: Path) -> None:
        try:
            entries = sorted(os.scandir(d), key=lambda e: e.name.lower())
        except OSError:
            return
        for e in entries:
            try:
                if e.is_dir(follow_symlinks=False):
                    if recursive and e.name.lower() not in SKIP_DIRS:
                        walk(Path(e.path))
                elif e.is_file(follow_symlinks=False):
                    ext = Path(e.name).suffix.lower()
                    if ext not in AUDIO_EXTS:
                        continue
                    sz = e.stat().st_size
                    if sz <= 0:
                        continue
                    rel = str(Path(e.path).relative_to(root))
                    out.append(SourceTrack(e.path, e.name, sz, ext, rel.lower()))
            except OSError:
                continue

    walk(root)
    return out


def pick_tracks(cands: list[SourceTrack], capacity_bytes: int,
                last_batch: list[str], avoid_repeat: bool = True,
                seed: str = "") -> list[SourceTrack]:
    """按容量随机挑选，尽量避开上一批；返回顺序即【写入顺序 = 随机播放顺序】。

    纯函数：便于自检，不碰任何磁盘。放不下的文件跳过继续找更小的，
    因此大文件不会把整批卡死。
    """
    if capacity_bytes <= 0 or not cands:
        return []
    rng = random.Random(seed or None)
    prev = {str(x).lower() for x in (last_batch or [])}
    if avoid_repeat:
        fresh = [t for t in cands if t.key not in prev]
        used = [t for t in cands if t.key in prev]
        rng.shuffle(fresh)
        rng.shuffle(used)
        pool = fresh + used                 # 没拷过的优先，库不够时才回落到旧歌
    else:
        pool = list(cands)
        rng.shuffle(pool)
    chosen: list[SourceTrack] = []
    total = 0
    for t in pool:
        if total + t.size > capacity_bytes:
            continue
        chosen.append(t)
        total += t.size
        if capacity_bytes - total < 64 * 1024:
            break
    return chosen


# -- 执行：拷贝即乱序 --------------------------------------------------------

def _audio_entries(rootp: Path) -> list[str]:
    """按目录项顺序枚举根目录音频（只读，不带盘符护栏，便于在临时目录自检）。"""
    out = []
    try:
        for e in os.scandir(rootp):
            if e.is_file() and Path(e.name).suffix.lower() in AUDIO_EXTS:
                out.append(e.name)
    except OSError:
        pass
    return out


def _copy_one(src: str, dst: Path, mtime: float) -> None:
    """4 MB 大块拷贝 + 大小校验 + 时间戳。慢速 USB 上减少小块提交开销。"""
    with open(src, "rb", buffering=0) as fsrc, open(dst, "wb", buffering=0) as fdst:
        while True:
            buf = fsrc.read(COPY_BUF)
            if not buf:
                break
            fdst.write(buf)
    expected = os.path.getsize(src)
    if dst.stat().st_size != expected:
        raise RuntimeError(f"拷贝校验失败：{dst.name}")
    os.utime(dst, (mtime, mtime))


def _target_name(src: SourceTrack, index: int, used: set[str]) -> str:
    """保留中文歌名，只换 001_ 编号前缀；处理超长名与重名。"""
    base = PREFIX_RE.sub("", src.name)
    base = BAD_CHARS_RE.sub("_", base).strip()
    if not base:
        base = "track" + src.ext
    if len(base) > 170:                       # FAT32 长名留足余量
        stem, ext = os.path.splitext(base)
        base = stem[:170 - len(ext)] + ext
    name = f"{index:03d}_{base}"
    if name.lower() in used:
        stem, ext = os.path.splitext(base)
        name = f"{index:03d}_{stem}_{index}{ext}"
    used.add(name.lower())
    return name


def _max_index(names: list[str]) -> int:
    mx = 0
    for n in names:
        m = re.match(r"^(\d{1,4})", n)
        if m:
            mx = max(mx, int(m.group(1)))
    return mx


def estimate_seconds(total_bytes: int, mbps: float = 1.0) -> int:
    """按保守吞吐估算耗时（默认 1 MB/s，慢速 FAT32 播放盘常见量级）。

    只用于确认弹窗里给用户一个数量级预期，实际速度取决于设备本身；
    界面会同时显示实时 MB/s 与剩余时间。可用 mbps 参数覆盖。
    """
    return int(total_bytes / (max(0.1, mbps) * 1024 * 1024))


def copy_shuffled(root: str, picked: list[SourceTrack], action: str,
                  progress, safe_names: bool = False) -> dict:
    """把 picked 按给定顺序写入 U 盘根目录 —— 写入顺序 == 目录项顺序 == 随机播放顺序。

    action='replace'：旧音频先同盘 move 进暂存（零拷贝），新歌全部写入并校验后才删除。
                      中途异常会删掉已写新歌并把旧歌移回，数据不丢。
    action='append' ：完全不碰旧文件，新歌按随机序追加在后面，编号接着往下排。

    注意：本函数刻意不做盘符护栏，方便在临时目录自检；
    调用方（UI）必须先做 safe_target_root + 设备白名单 + 用户二次确认。
    """
    if action not in ("replace", "append"):
        raise ValueError(f"未知动作：{action}")
    if not picked:
        raise RuntimeError("没有可拷贝的音频")
    rootp = Path(root)
    swap = rootp / SWAP_DIR
    need = sum(t.size for t in picked)
    free = shutil.disk_usage(root).free
    if need >= free - 16 * 1024 * 1024:
        raise RuntimeError(
            f"U 盘剩余空间不足：需要 {need / 1024**3:.2f} GB，可用 {free / 1024**3:.2f} GB")

    recover_swap(rootp, progress)              # 上次中断的残留先恢复
    if swap.exists():
        raise RuntimeError(f"暂存目录 {SWAP_DIR} 无法清理，请检查 U 盘")
    old_names = _audio_entries(rootp)
    used: set[str] = set()
    start_no = 1
    if action == "replace":
        swap.mkdir()
        for n in old_names:
            p = rootp / n
            clear_readonly(p)
            p.rename(swap / n)
    else:
        used = {n.lower() for n in old_names}
        start_no = _max_index(old_names) + 1

    written: list[Path] = []
    total_bytes = sum(t.size for t in picked)
    done_bytes = 0
    t_start = time.perf_counter()
    m0 = time.time() - len(picked) * 2 - 10   # 时间戳按序递增，步长 2 秒（FAT32 精度）
    try:
        for i, t in enumerate(picked):
            if safe_names:
                name = f"{start_no + i:03d}{t.ext}"
                if name.lower() in used:
                    name = f"{start_no + i:03d}_{i}{t.ext}"
                used.add(name.lower())
            else:
                name = _target_name(t, start_no + i, used)
            dst = rootp / name
            if dst.exists():
                raise RuntimeError(f"目标名冲突：{name}")
            _copy_one(t.path, dst, m0 + i * 2)
            written.append(dst)
            done_bytes += t.size
            elapsed = time.perf_counter() - t_start
            speed = done_bytes / elapsed if elapsed > 0 else 0
            eta = (total_bytes - done_bytes) / speed if speed > 0 else -1
            eta_txt = f" · 还需约 {eta / 60:.1f} 分钟" if eta >= 0 else ""
            progress(i + 1, len(picked),
                     f"写入 {i + 1}/{len(picked)} · {speed / 1024 / 1024:.2f} MB/s{eta_txt}")
    except Exception:
        for p in written:
            try:
                p.unlink()
            except OSError:
                pass
        if action == "replace":
            recover_swap(rootp, progress)
        raise

    removed = 0
    if action == "replace":
        for p in list(swap.iterdir()):
            if p.is_file():
                clear_readonly(p)
                p.unlink()
                removed += 1
        try:
            swap.rmdir()
        except OSError:
            pass
        if MANIFEST.is_file():              # 旧还原清单已失效，归档而不是让「一键还原」误读
            archive = DATA / f"last_manifest_before_copy_{datetime.now():%Y%m%d_%H%M%S}.json"
            try:
                MANIFEST.replace(archive)
                log(f"旧还原清单已归档：{archive.name}（替换模式已删除原音频）")
            except OSError as exc:
                log(f"旧还原清单归档失败：{exc}")

    actual = _audio_entries(rootp)
    expected = [p.name for p in written]
    verified = (actual == expected) if action == "replace" else (
        actual[-len(expected):] == expected if expected else True)
    log(f"随机拷贝完成：{action} · {len(written)} 首 · {total_bytes / 1024**3:.2f} GB · "
        f"删除旧歌 {removed} 首 · 目录项顺序{'校验通过' if verified else '校验未通过'}")
    return {"count": len(written), "bytes": total_bytes, "action": action,
            "removed": removed, "verified": verified, "names": expected,
            "seconds": time.perf_counter() - t_start}


# --------------------------------------------------------------------------- 只读诊断

def first_by_rules(tracks: list[Track]) -> dict:
    """三种候选播放规则各自的第一首（纯函数，与文件系统实现无关）。

    FAT32 目录项是线性表，scan 返回顺序即目录项顺序；NTFS 目录按名字索引，
    枚举顺序可能等于字典序 —— 所以本函数只负责「按给定顺序取首曲」，不猜设备。
    """
    if not tracks:
        return {}
    by_dir = list(tracks)
    by_name = sorted(tracks, key=lambda t: t.orig_name.casefold())
    by_time = sorted(tracks, key=lambda t: (t.mtime, t.orig_name.casefold()))
    return {
        "A 文件名字典序": by_name[0].orig_name,
        "B FAT 目录项 / 拷贝顺序": by_dir[0].orig_name,
        "C 修改时间升序": by_time[0].orig_name,
    }


def diagnose(root: str, recursive: bool = False) -> dict:
    """纯只读诊断：算出三种候选播放规则各自的第一首，绝不动任何文件。

    网上常见的「改名加 01_ 序号」教程只对按文件名字典序读盘的固件有效。
    把三种候选首曲摆出来，用户戴设备听一次就能判定，不用拆机也不用猜。
    """
    t0 = time.perf_counter()
    fp = device_fingerprint(root)
    tracks = scan(root, recursive, guard=False)
    result = {
        "root": root,
        "ok": bool(tracks),
        "serial": fp["serial"],
        "label": fp["label"],
        "fs": fp["fs"],
        "total": fp["total"],
        "free": 0,
        "volume": volume_info(root),
        "audio_count": len(tracks),
        "total_bytes": sum(t.size for t in tracks),
        "readonly_count": sum(1 for t in tracks if t.readonly),
        "long_name_count": sum(1 for t in tracks
                               if any(ord(c) > 127 for c in t.orig_name)
                               or len(t.orig_name) > 12),
        "first": {},
        "distinct": 0,
        "elapsed_ms": 0.0,
    }
    try:
        result["free"] = shutil.disk_usage(root).free
    except OSError:
        pass
    if tracks:
        result["first"] = first_by_rules(tracks)
        result["distinct"] = len(set(result["first"].values()))
    result["elapsed_ms"] = (time.perf_counter() - t0) * 1000
    return result


def diagnose_text(d: dict) -> str:
    """诊断结果 → 可展示 / 可复制的报告文本（纯函数，便于单测）。"""
    lines = [
        f"{APP_NAME} v{APP_VERSION} · 只读诊断报告",
        f"生成时间：{datetime.now():%Y-%m-%d %H:%M:%S}",
        "本次诊断只读取目录与文件属性，没有创建、修改或删除任何文件。",
        "",
        "【设备】",
        f"  盘符：{d['root']}   卷序列号：{d['serial'] or '读取失败'}   卷标：{d['label'] or '（空）'}",
        f"  文件系统 / 空间：{d['volume']}",
        f"  容量：{d['total'] / 1024**3:.1f} GB   可用：{d['free'] / 1024**3:.1f} GB",
        "",
        "【歌单】",
        f"  音频文件：{d['audio_count']} 首 / {d['total_bytes'] / 1024**3:.2f} GB",
        f"  长名或中文名：{d['long_name_count']} 首   只读属性：{d['readonly_count']} 首",
        f"  扫描耗时：{d['elapsed_ms']:.0f} ms（只读）",
        "",
    ]
    if not d["ok"]:
        lines += ["【结论】", "  未找到音频文件，请先往 U 盘根目录放几首歌再来诊断。", ""]
    else:
        lines += ["【三种可能的播放规则 · 各自的第一首】"]
        for k, v in d["first"].items():
            lines.append(f"  {k}：")
            lines.append(f"      {v}")
        lines += [""]
        if d["distinct"] >= 2:
            lines += [
                "【怎么判定】",
                "  安全弹出 U 盘 → 让设备断电重连 → 听第一首是哪首，对照上表即可。",
                "  若第一首 = B，说明设备按拷贝顺序读盘：改文件名 / 编号完全无效，",
                "  只能用「极速重排」或「清盘重写」改变顺序。",
                "  若第一首 = A，「仅重命名」就够用；= C 则按修改时间排。",
            ]
        else:
            lines += [
                "【怎么判定】",
                "  三种规则算出的首曲相同，靠「听第一首」暂时区分不出来。",
                "  可以直接跑一次「极速重排」（数秒、零拷贝），再拔插听第一首是否变化；",
                "  没变就点「一键还原」再改试「清盘重写」。",
            ]
        lines += [
            "",
            "【提示】",
            "  还有极少数固件按物理簇号读取；这种情况下只有「清盘重写」能改变顺序。",
            "  无论选哪种模式，正式执行前都会再弹一次确认，本诊断页不会写盘。",
            "",
        ]
    return "\n".join(lines)


def source_urls() -> dict:
    """源码地址优先读 assets/repo.json —— 发布者改文本文件即可，不必重新打包。"""
    urls = {"primary": SOURCE_URL, "mirror": SOURCE_URL_MIRROR}
    try:
        raw = json.loads((ASSETS / "repo.json").read_text(encoding="utf-8"))
        urls["primary"] = str(raw.get("primary") or urls["primary"])
        urls["mirror"] = str(raw.get("mirror") or urls["mirror"])
    except Exception:
        pass
    return urls


# --------------------------------------------------------------------------- GUI
# 视觉系统：浅色底 / 白色卡片 / 单一强调色 / 严格字阶 / 大留白。
# 设计原则：一个窗口只回答「今天要做什么」；参数退到设置；消除一切假状态。

BG, CARD, INK = "#F5F5F7", "#FFFFFF", "#1D1D1F"
INK2, INK3 = "#6E6E73", "#A1A1A6"
ACCENT, ACCENT_DARK = "#0071E3", "#0062C4"
LINE, OK_GREEN, WARN = "#E3E3E8", "#248A3D", "#B25000"

F_H1 = ("Microsoft YaHei UI", 21, "bold")
F_H2 = ("Microsoft YaHei UI", 14, "bold")
F_BODY = ("Microsoft YaHei UI", 11)
F_SUB = ("Microsoft YaHei UI", 10)
F_FINE = ("Microsoft YaHei UI", 9)
F_BTN = ("Microsoft YaHei UI", 12, "bold")

HELP_TEXT = "只读诊断不会改动任何文件；只有已绑定的播放设备才允许写入。"
DISCLAIMER = (
    "本工具会移动、重命名或删除 U 盘上的音频文件，使用前请备份重要数据。\n"
    "所有写操作都需要手动执行并二次确认，且只对已绑定的播放设备生效；"
    "插盘只提醒，绝不自动写盘。\n"
    "作者不对数据丢失、设备损坏或任何间接损失负责。"
)
AUTO_POLL_MS = 2000          # 插盘检测间隔
AUTO_MIN_TRACKS = 5          # 音频数低于此值不自动触发（防误认空盘）


def setup_theme(root):
    """全局样式。tk 原生控件自行着色，ttk 控件统一走这里的样式表。"""
    if ttk is None:
        return None
    st = ttk.Style(root)
    if "clam" in st.theme_names():
        st.theme_use("clam")
    st.configure(".", background=BG, foreground=INK, font=F_BODY)
    st.configure("Bg.TFrame", background=BG)
    st.configure("Card.TFrame", background=CARD)
    st.configure("Card.TLabel", background=CARD, foreground=INK, font=F_BODY)
    st.configure("Sub.TLabel", background=CARD, foreground=INK2, font=F_SUB)
    st.configure("BgSub.TLabel", background=BG, foreground=INK2, font=F_SUB)
    st.configure("Primary.TButton", background=ACCENT, foreground="#FFFFFF",
                 font=F_BTN, borderwidth=0, relief="flat", padding=(28, 12))
    st.map("Primary.TButton",
           background=[("active", ACCENT_DARK), ("disabled", "#C4DCF5")],
           foreground=[("disabled", "#FFFFFF")])
    st.configure("Ghost.TButton", background=CARD, foreground=ACCENT,
                 font=F_BODY, borderwidth=0, relief="flat", padding=(10, 6))
    st.map("Ghost.TButton", background=[("active", "#EDF4FE")])
    st.configure("Bare.TButton", background=BG, foreground=INK2,
                 font=F_SUB, borderwidth=0, relief="flat", padding=(8, 4))
    st.map("Bare.TButton", background=[("active", "#E8E8ED")],
           foreground=[("active", INK)])
    st.configure("TProgressbar", background=ACCENT, troughcolor=LINE,
                 borderwidth=0, thickness=4)
    st.configure("Treeview", background=CARD, fieldbackground=CARD,
                 foreground=INK, borderwidth=0, rowheight=24, font=F_SUB)
    st.configure("Treeview.Heading", background="#FAFAFC", foreground=INK2,
                 font=F_SUB, borderwidth=0, relief="flat")
    st.configure("TCombobox", fieldbackground=CARD, background=CARD,
                 foreground=INK, borderwidth=0, arrowcolor=INK2, padding=6)
    # 旧对话框仍在用的基础控件与样式别名，一并统一到同一套配色
    for name in ("TFrame", "TLabel", "TLabelframe", "TLabelframe.Label",
                 "TRadiobutton", "TCheckbutton", "TButton", "TEntry", "TSpinbox"):
        st.configure(name, background=BG, foreground=INK, font=F_BODY)
    st.configure("TButton", padding=(10, 6), borderwidth=0, relief="flat")
    st.map("TButton", background=[("active", "#E8E8ED")])
    st.configure("Title.TLabel", background=BG, foreground=INK, font=F_H2)
    st.configure("Hint.TLabel", background=BG, foreground=INK2, font=F_SUB)
    st.configure("Go.TButton", background=ACCENT, foreground="#FFFFFF",
                 font=F_BTN, borderwidth=0, relief="flat", padding=(16, 9))
    st.map("Go.TButton", background=[("active", ACCENT_DARK),
                                     ("disabled", "#C4DCF5")])
    return st


def ui_label(master, text, font=F_BODY, fg=INK, bg=CARD, **kw):
    """统一的文字标签：默认左对齐、不换行、无边框。"""
    return tk.Label(master, text=text, font=font, fg=fg, bg=bg,
                    anchor="w", justify="left", bd=0, **kw)


def ui_card(master, pad=20):
    """白色卡片 + 1px 细边 + 大留白。返回 (外框, 内容 Frame)。"""
    outer = tk.Frame(master, bg=CARD, highlightbackground=LINE,
                     highlightthickness=1, bd=0)
    inner = tk.Frame(outer, bg=CARD)
    inner.pack(fill="both", expand=True, padx=pad, pady=pad)
    return outer, inner


def ui_button(master, text, command, kind="primary", padx=30):
    """扁平按钮：primary 填充蓝；link 是无边框文字按钮。"""
    if kind == "primary":
        return tk.Button(master, text=text, command=command, font=F_BTN,
                         bg=ACCENT, fg="#FFFFFF", activebackground=ACCENT_DARK,
                         activeforeground="#FFFFFF", relief="flat", bd=0,
                         padx=padx, pady=11, cursor="hand2", highlightthickness=0)
    if kind == "link":
        return tk.Button(master, text=text, command=command, font=F_BODY,
                         bg=master.cget("bg"), fg=ACCENT,
                         activebackground=master.cget("bg"),
                         activeforeground=ACCENT_DARK, relief="flat", bd=0,
                         padx=6, pady=4, cursor="hand2", highlightthickness=0)
    return tk.Button(master, text=text, command=command, font=F_SUB,
                     bg=master.cget("bg"), fg=INK2,
                     activebackground=master.cget("bg"), activeforeground=INK,
                     relief="flat", bd=0, padx=6, pady=3,
                     cursor="hand2", highlightthickness=0)


def ui_divider(master, bg=CARD):
    return tk.Frame(master, bg=LINE, height=1)


def status_dot(master, bg=CARD, color=INK3, size=9):
    """状态圆点，替代原来的 emoji 图标。"""
    c = tk.Canvas(master, width=size, height=size, bg=bg,
                  highlightthickness=0, bd=0)
    c.create_oval(1, 1, size - 1, size - 1, fill=color, outline=color)
    return c



def auto_decision(was_present: bool, present: bool, busy: bool,
                  elapsed_s: float, cooldown_min: int) -> str:
    """自动洗牌的触发判断（纯函数，便于单测）：只在「从无到有」的插盘边沿触发一次。"""
    if not (present and not was_present):
        return "none"
    if busy:
        return "busy"
    if elapsed_s < cooldown_min * 60:
        return "cooldown"
    return "run"


_AppBase = tk.Tk if tk is not None else object


class App(_AppBase):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w = min(820, max(720, sw - 160))
        h = min(580, max(500, sh - 150))
        self.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 5)}")
        self.minsize(720, 500)
        self.configure(bg=BG)

        self._closing = False
        self.bind("<Control-Return>", lambda e: self._execute())
        self.bind("<F5>", lambda e: self._shuffle())
        self.bind("<Control-z>", lambda e: self._restore())
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        self.cfg = load_config()
        self.root_var = tk.StringVar()
        self.mode = tk.StringVar(value=str(self.cfg.get("shuffle_mode") or "fast"))
        self.safe_names = tk.BooleanVar(value=bool(self.cfg.get("safe_names")))
        self.recursive = tk.BooleanVar(value=bool(self.cfg.get("scan_recursive")))
        self.seed = tk.StringVar(value=str(self.cfg.get("seed") or ""))
        self.auto = tk.BooleanVar(value=bool(self.cfg.get("remind_on_insert")))
        self.cooldown_var = tk.IntVar(value=10)
        self.status = tk.StringVar(value="尚未改动任何文件")
        self.tracks: list[Track] = []
        self.order: list[Track] = []
        self.plan: list[dict] = []
        self.busy = False
        self.q: queue.Queue = queue.Queue()
        # 插盘提醒状态：只弹提示，绝不自动写盘
        self.auto_serial = ""
        self.auto_root = ""
        self.auto_last = 0.0
        self.auto_present = False
        self._notify_open = False
        self._copy_win = None
        self._diag_win = None
        self._about_win = None
        self._settings_win = None
        self._setup_win = None
        self.detail_shown = False

        self._build_ui()
        self._refresh_drives()
        self._update_device_status()
        self._pump_id = self.after(100, self._pump)
        self._tick_id = self.after(AUTO_POLL_MS, self._auto_tick)
        # 一次性引导独立出现，不占用日常界面
        self.after(350, self._maybe_setup)

    # -- 布局 ----------------------------------------------------------------
    def _build_ui(self):
        """日常界面只有一个主操作、一张设备卡片、一行状态。其余全部收进设置 / 引导。"""
        setup_theme(self)

        top = tk.Frame(self, bg=BG)
        top.pack(fill="x", padx=32, pady=(26, 18))
        ui_label(top, "ShuffleStick", F_H2, INK, BG).pack(side="left")
        ui_label(top, "U 盘歌单乱序助手", F_SUB, INK3, BG).pack(side="left", padx=(10, 0))
        ui_button(top, "关于", self._open_about, "quiet").pack(side="right")
        ui_button(top, "设置", self._open_settings, "quiet").pack(side="right", padx=(0, 14))

        # 设备卡片：唯一的状态区，用圆点代替 emoji
        card, dev = ui_card(self, pad=18)
        r1 = tk.Frame(dev, bg=CARD)
        r1.pack(fill="x")
        self.dev_dot = status_dot(r1, CARD, INK3)
        self.dev_dot.pack(side="left", padx=(0, 9))
        self.dev_lbl = ui_label(r1, "正在检测设备…", F_BODY, INK, CARD)
        self.dev_lbl.pack(side="left")
        ui_button(r1, "刷新", self._refresh_drives, "quiet").pack(side="right")
        self.drive_cb = ttk.Combobox(r1, textvariable=self.root_var, width=6,
                                     state="readonly")
        self.drive_cb.pack(side="right", padx=(0, 12))
        self.drive_cb.bind("<<ComboboxSelected>>", lambda _: self._rescan())
        r2 = tk.Frame(dev, bg=CARD)
        r2.pack(fill="x", pady=(9, 0))
        self.info_lbl = ui_label(r2, "", F_SUB, INK2, CARD)
        self.info_lbl.pack(side="left")
        self.bind_btn = ui_button(r2, "绑定为播放设备", self._bind_device, "link")
        self.bind_btn.pack(side="right")
        card.pack(fill="x", padx=32, pady=(0, 20))

        # 底部状态栏先占位，保证任何窗口尺寸下都可见
        self.foot = tk.Frame(self, bg=BG)
        self.foot.pack(side="bottom", fill="x", padx=32, pady=(12, 20))
        tk.Label(self.foot, textvariable=self.status, font=F_FINE,
                 fg=INK2, bg=BG, anchor="w").pack(side="left")
        self.detail_btn = ui_button(self.foot, "查看顺序详情",
                                    self._toggle_details, "quiet")
        self.detail_btn.pack(side="right")
        self.pbar = ttk.Progressbar(self, mode="determinate", maximum=100)

        self.center = tk.Frame(self, bg=BG)
        self.center.pack(fill="both", expand=True, padx=32)

        # 简视图：一句话价值 + 一个主按钮 + 三个低权重次要操作
        self.simple = tk.Frame(self.center, bg=BG)
        self.hero_title = ui_label(self.simple, "给歌单换个顺序", F_H1, INK, BG)
        self.hero_title.pack(pady=(12, 0))
        self.hero_sub = ui_label(
            self.simple,
            "从电脑音频库随机挑一批歌拷进 U 盘，写入顺序就是播放顺序。",
            F_BODY, INK2, BG)
        self.hero_sub.pack(pady=(10, 0))
        self.copy_btn = ui_button(self.simple, "换一批歌", self._open_copy_dialog)
        self.copy_btn.pack(pady=(30, 0))
        links = tk.Frame(self.simple, bg=BG)
        links.pack(pady=(26, 0))
        self.run_btn = ui_button(links, "打乱现有歌单", self._execute, "link")
        self.run_btn.pack(side="left", padx=10)
        self.rst_btn = ui_button(links, "还原上一次", self._restore, "link")
        self.rst_btn.pack(side="left", padx=10)
        self.diag_btn = ui_button(links, "只读诊断", self._open_diagnose, "link")
        self.diag_btn.pack(side="left", padx=10)
        self.simple.pack(fill="both", expand=True)

        # 详情视图：与简视图互斥，默认不出现
        self.detail = tk.Frame(self.center, bg=BG)
        lists = tk.Frame(self.detail, bg=BG)
        self.left = self._make_tree(lists, "当前顺序")
        self.right = self._make_tree(lists, "随机预览（未写入）")
        self.left.pack(side="left", fill="both", expand=True, padx=(0, 6))
        self.right.pack(side="right", fill="both", expand=True, padx=(6, 0))
        lists.pack(fill="both", expand=True)

    # -- 视图切换 / 弹窗入口 -------------------------------------------------
    def _toggle_details(self):
        self.detail_shown = not self.detail_shown
        if self.detail_shown:
            self.simple.pack_forget()
            self.detail.pack(fill="both", expand=True)
            self.detail_btn.configure(text="返回")
        else:
            self.detail.pack_forget()
            self.simple.pack(fill="both", expand=True)
            self.detail_btn.configure(text="查看顺序详情")

    def _maybe_setup(self):
        if self._closing:
            return
        # 老用户已经绑定过设备，直接标记为已完成引导，不打扰
        if self.cfg.get("device_whitelist"):
            if not self.cfg.get("onboarded"):
                self.cfg["onboarded"] = True
                save_config(self.cfg)
            return
        if not self.cfg.get("onboarded"):
            self._open_setup()

    def _open_setup(self):
        if self._setup_win is not None and self._setup_win.winfo_exists():
            self._setup_win.lift()
            return
        self._setup_win = SetupDialog(self)

    def _open_settings(self):
        if self._settings_win is not None and self._settings_win.winfo_exists():
            self._settings_win.lift()
            return
        self._settings_win = SettingsDialog(self)

    def _make_tree(self, parent, title):
        frm = tk.Frame(parent, bg=CARD, highlightbackground=LINE,
                       highlightthickness=1, bd=0)
        ui_label(frm, title, F_SUB, INK2, CARD).pack(anchor="w", padx=14, pady=(12, 6))
        body = tk.Frame(frm, bg=CARD)
        body.pack(fill="both", expand=True, padx=14, pady=(0, 12))
        cols = ("no", "name", "size")
        tv = ttk.Treeview(body, columns=cols, show="headings", selectmode="browse")
        tv.heading("no", text="#"); tv.column("no", width=44, anchor="center", stretch=False)
        tv.heading("name", text="文件名"); tv.column("name", width=210, anchor="w")
        tv.heading("size", text="大小"); tv.column("size", width=70, anchor="e", stretch=False)
        sb = ttk.Scrollbar(body, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb.set)
        tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        return frm

    @staticmethod
    def _tree_of(frm):
        """递归找 Treeview（卡片化之后表格多了一层容器）。"""
        stack = [frm]
        while stack:
            w = stack.pop()
            if isinstance(w, ttk.Treeview):
                return w
            stack.extend(w.winfo_children())
        raise RuntimeError("tree missing")

    # -- 数据 ----------------------------------------------------------------
    def _refresh_drives(self):
        drives = list_drives()
        self.drive_cb["values"] = drives
        cur = self.root_var.get()
        if cur not in drives:
            self.root_var.set(preferred_drive(drives))
        if not self.root_var.get():
            # U 盘没插时不要默认停在 D:\ 之类的固定盘上，免得对着空列表点执行
            self.info_lbl.configure(text="未检测到可移动 U 盘")
            self.status.set("未检测到 U 盘 · 插回设备后会自动切换（也可手动选盘）")
            self._fill(self._tree_of(self.left), [])
            self._fill(self._tree_of(self.right), [])
            self._update_device_status()
            return
        self._rescan()
        self._update_device_status()

    def _rescan(self):
        root = self.root_var.get()
        if not root:
            return
        try:
            self.tracks = scan(root, self.recursive.get())
            self.info_lbl.configure(text=f"{volume_info(root)} · 识别到 {len(self.tracks)} 首音频")
            self.status.set(f"只读扫描完成：{len(self.tracks)} 首 · 未改动任何文件")
            self._fill(self._tree_of(self.left),
                       [(i + 1, t.orig_name, t.size) for i, t in enumerate(self.tracks)])
            # 打开即给出一批随机预览，避免对着原顺序白跑一次清盘重写
            try:
                self.order = make_order(self.tracks, self.seed.get())
            except RuntimeError:
                self.order = list(self.tracks)
            self._preview()
            self.status.set(f"已扫描 {len(self.tracks)} 首 · 未改动任何文件")
            # 有备份目录但没有还原清单 = 上次清盘重写中断，此时不要基于残缺歌单重新洗
            try:
                if not MANIFEST.is_file() and any(BACKUP_ROOT.iterdir()):
                    self.status.set(
                        "检测到未完成的清盘重写备份：U 盘可能只恢复了一部分，"
                        "请等原任务跑完或点「一键还原」，不要重新洗牌")
            except OSError:
                pass
        except Exception as exc:
            messagebox.showerror("扫描失败", str(exc))

    def _shuffle(self):
        if not self.tracks:
            messagebox.showinfo("提示", "没有扫描到音频文件")
            return
        try:
            self.order = make_order(self.tracks, self.seed.get())
            self._preview()
            self.status.set("已生成新的随机序列 · 仍只是预览，未写入 U 盘")
        except Exception as exc:
            messagebox.showerror("洗牌失败", str(exc))

    def _plan(self):
        return build_plan(self.order, self.safe_names.get())

    def _preview(self):
        if not self.order:
            return
        self.plan = self._plan()
        self._fill(self._tree_of(self.right),
                   [(p["seq"], p["dst"], p["size"]) for p in self.plan])

    def _fill(self, tv, rows):
        tv.delete(*tv.get_children())
        for no, name, size in rows:
            tv.insert("", "end", values=(f"{no:03d}", name, f"{size / 1024**2:.1f} MB"))

    # -- 执行 ----------------------------------------------------------------
    def _set_busy(self, busy):
        self.busy = busy
        state = "disabled" if busy else "normal"
        for btn in (self.run_btn, self.rst_btn, self.copy_btn, self.diag_btn):
            btn.configure(state=state)   # 写盘期间目录在变，暂时禁用诊断
        if busy:
            self.pbar.pack(side="bottom", fill="x", padx=32, pady=(0, 4),
                           before=self.foot)
        else:
            self.pbar.pack_forget()
            # 恢复「按绑定状态决定」的按钮可用性，别把未绑定盘的写操作放开
            self._update_device_status()

    def _progress(self, done, total, text):
        self.q.put(("progress", (done, total, text)))

    def _on_close(self):
        if self.busy and not messagebox.askyesno(
                "正在写 U 盘",
                "洗牌还没完成，现在关闭可能让 U 盘处于中间状态。\n"
                "建议等进度条走完（可用「一键还原」恢复）。确定强制退出吗？"):
            return
        self._closing = True
        for aid in (getattr(self, "_pump_id", None), getattr(self, "_tick_id", None)):
            if aid:
                try:
                    self.after_cancel(aid)
                except Exception:
                    pass
        self.destroy()

    def _pump(self):
        if self._closing:
            return
        try:
            while True:
                kind, payload = self.q.get_nowait()
                if kind == "progress":
                    done, total, text = payload
                    self.pbar["value"] = max(0, min(100, 100 * done / max(1, total)))
                    self.status.set(text)
                elif kind == "done":
                    ok, msg, quiet = payload
                    self._set_busy(False)
                    if self.auto.get() and self.auto_root:
                        # 任务结束后同步真实插拔状态，避免下一轮误判上升沿
                        self.auto_present = (
                            os.path.isdir(self.auto_root)
                            and volume_serial(self.auto_root) == self.auto_serial)
                    self.pbar["value"] = 100 if ok else 0
                    self.status.set(msg)
                    if quiet:
                        log(f"自动任务结果：{'成功' if ok else '失败'} · {msg}")
                    elif ok:
                        messagebox.showinfo("完成", msg)
                    else:
                        messagebox.showerror("失败", msg)
                    if ok:
                        self._rescan()
                        self.status.set(
                            ("自动洗牌完成 · 可安全弹出 U 盘：" if quiet else "洗牌完成 · ")
                            + msg.splitlines()[0])
        except queue.Empty:
            pass
        self._pump_id = self.after(80, self._pump)

    def _run_bg(self, fn, quiet=False):
        self._set_busy(True)
        self.pbar["value"] = 0
        def worker():
            try:
                with keep_awake():          # 长任务期间阻止系统睡眠/休眠
                    res = fn()
                self.q.put(("done", (True, res, quiet)))
            except Exception as exc:
                log(f"操作失败：{exc}")
                self.q.put(("done", (
                    False, f"操作失败：{exc}\n\nU 盘可能处于中间状态，可尝试「一键还原」。", quiet)))
        threading.Thread(target=worker, daemon=True).start()

    # -- 设备白名单：所有写操作的统一入口校验 -------------------------------
    def _require_headset(self, root: str) -> bool:
        """未绑定 / 非播放设备一律拒绝写入，避免误动存文件的普通 U 盘。"""
        fp = device_fingerprint(root)
        if match_headset(fp, self.cfg):
            return True
        messagebox.showwarning(
            "设备未绑定 · 已阻止写操作",
            f"当前目标：{root}\n"
            f"卷序列号：{fp['serial'] or '读取失败'} · 卷标：{fp['label'] or '（空）'}\n"
            f"容量：{fp['total'] / 1024**3:.1f} GB · {fp['fs']} · 音频 {fp['audio_count']} 首\n\n"
            "为防止误操作存文件的普通 U 盘，只有绑定过的播放设备才允许写入。\n"
            "请确认这就是你要放歌的那台设备，点主界面的「开始设置」完成绑定。")
        return False

    def _set_dot(self, color: str) -> None:
        if not hasattr(self, "dev_dot"):
            return
        self.dev_dot.delete("all")
        self.dev_dot.create_oval(1, 1, 8, 8, fill=color, outline=color)

    def _update_device_status(self) -> None:
        """设备状态、主按钮文案、引导语统一由一个状态驱动，界面自己说明下一步。"""
        if not hasattr(self, "dev_lbl"):
            return
        root = self.root_var.get()
        bound = False
        if root and os.path.isdir(root):
            fp = device_fingerprint(root)
            rec = match_headset(fp, self.cfg)
            bound = bool(rec)
            if rec:
                self._set_dot(OK_GREEN)
                self.dev_lbl.configure(
                    text=f"已连接播放设备 · {rec.get('model') or '播放设备'}")
                self.bind_btn.configure(text="重新绑定")
            else:
                self._set_dot(WARN)
                self.dev_lbl.configure(text="未绑定的 U 盘 · 只读，不会写入")
                self.bind_btn.configure(text="绑定为播放设备")
        else:
            self._set_dot(INK3)
            self.dev_lbl.configure(text="未检测到 U 盘")
            self.bind_btn.configure(text="绑定为播放设备")

        if not getattr(self, "copy_btn", None):
            return
        # 未绑定时禁用写操作，只留只读诊断可点；界面自己说清下一步
        write_state = "normal" if (bound and not self.busy) else "disabled"
        self.run_btn.configure(state=write_state)
        self.rst_btn.configure(state=write_state)
        if bound:
            self.hero_title.configure(text="给歌单换个顺序")
            self.hero_sub.configure(
                text="从电脑音频库随机挑一批歌拷进 U 盘，写入顺序就是播放顺序。")
            self.copy_btn.configure(text="换一批歌",
                                    command=self._open_copy_dialog,
                                    bg=ACCENT, state=write_state)
        else:
            self.hero_title.configure(text="先花十秒认识你的设备")
            self.hero_sub.configure(
                text="绑定后只有这块盘允许写入，其它 U 盘一律忽略，全程不会自动改动文件。")
            self.copy_btn.configure(text="开始设置", command=self._open_setup,
                                    bg=ACCENT, state="normal")

    def _bind_device(self) -> None:
        root = self.root_var.get()
        if not root or not os.path.isdir(root):
            messagebox.showwarning("无法绑定", "请先插上播放设备并选中对应盘符")
            return
        fp = device_fingerprint(root)
        if not fp["serial"]:
            messagebox.showerror("无法绑定", "读取不到卷序列号")
            return
        model = usb_device_model(root)
        ok = messagebox.askyesno(
            "绑定播放设备 · 请核对设备",
            f"盘符：{root}\n"
            f"设备型号：{model or '（未读到，可继续）'}\n"
            f"卷序列号：{fp['serial']}   卷标：{fp['label'] or '（空）'}\n"
            f"容量：{fp['total'] / 1024**3:.1f} GB · {fp['fs']} · 当前音频 {fp['audio_count']} 首\n\n"
            "请确认这台设备【就是你要放歌的那台】，不是存文件的普通 U 盘。\n"
            "绑定后只有这块盘允许写入；其它 U 盘插入一律忽略。\n\n"
            "确认绑定？")
        if not ok:
            return
        try:
            rec = bind_headset(root, self.cfg, model=model)
        except Exception as exc:
            messagebox.showerror("绑定失败", str(exc))
            return
        self._update_device_status()
        self.status.set(f"已绑定播放设备：{root} / {rec['serial']}")
        messagebox.showinfo("绑定成功",
                            f"已记住这块播放设备：\n{rec['model']} / {rec['serial']}\n\n"
                            "以后只有它会被允许执行洗牌和随机拷贝。")

    # -- 插盘仅提醒（绝不自动写盘） -----------------------------------------
    def _toggle_auto(self):
        enabled = self.auto.get()
        self.cfg["remind_on_insert"] = enabled
        save_config(self.cfg)
        if not enabled:
            self.status.set("插盘提醒已关闭 · 工具不会自动做任何事")
            log("插盘提醒关闭")
            return
        root = self.root_var.get()
        rec = match_headset(device_fingerprint(root), self.cfg) if root else None
        if not rec:
            messagebox.showwarning(
                "请先绑定播放设备",
                "插盘提醒只对已绑定的播放设备生效，避免误认存文件的普通 U 盘。\n\n"
                "请先插上设备，点右上角「🔗 绑定为播放设备」核对设备后再勾选。")
            self.auto.set(False)
            self.cfg["remind_on_insert"] = False
            save_config(self.cfg)
            return
        self.auto_root = root
        self.auto_serial = rec["serial"]
        self.auto_last = 0.0
        self.auto_present = os.path.isdir(root)   # 当前这次插入不提醒，下次插拔才弹
        self.status.set(f"插盘提醒已开启 · 仅弹提示，不会自动写盘 · {rec['serial']}")
        log(f"插盘提醒启用 root={root} serial={rec['serial']}（只提醒不执行）")

    def _auto_tick(self):
        """轮询检测「从无到有」的插盘边沿；检测到后只弹提示，不执行任何写操作。"""
        if self._closing:
            return
        try:
            # U 盘插回 / 拔走 / 换盘符时自动跟随；只在目标为空或已失效时切，
            # 不覆盖用户手动选中的盘（含固定盘）
            if not self.busy:
                cur = self.root_var.get()
                if not cur or not os.path.isdir(cur):
                    rem = preferred_drive(list_drives())
                    if rem != cur:
                        self._refresh_drives()
                        log(f"U 盘状态变化：目标已切到 {rem or '（等待插入）'}")
            # busy 期间目录会被清空/重建，必须冻结检测，否则会被误判成再次插入
            if self.auto.get() and not self.busy:
                root = self.auto_root
                present = False
                if root and os.path.isdir(root) and volume_serial(root) == self.auto_serial:
                    try:
                        present = len(scan(root, self.recursive.get())) >= AUTO_MIN_TRACKS
                    except Exception:
                        present = False
                elapsed = time.time() - self.auto_last
                cd = self.cooldown_var.get()
                decision = auto_decision(self.auto_present, present, self.busy, elapsed, cd)
                self.auto_present = present
                if decision == "run":
                    self._auto_notify(root)
                elif decision == "cooldown":
                    log(f"插盘提醒跳过：冷却中（{int(cd * 60 - elapsed)} 秒后可再提醒）")
        except Exception as exc:
            log(f"插盘轮询异常：{exc}")
        self._tick_id = self.after(AUTO_POLL_MS, self._auto_tick)

    def _auto_notify(self, root: str) -> None:
        """检测到播放设备插入：弹提示让用户自己决定，绝不自动动手。"""
        self.auto_last = time.time()
        if self._notify_open:
            return
        fp = device_fingerprint(root)
        rec = match_headset(fp, self.cfg)
        if not rec:
            self.status.set(f"检测到其它 U 盘（{fp['serial']}）· 非播放设备，已忽略")
            log(f"非白名单 U 盘插入，已忽略：{root} / {fp['serial']}")
            return
        self._notify_open = True
        win = tk.Toplevel(self)
        win.title("检测到播放设备")
        win.geometry("400x210")
        win.transient(self)
        win.configure(bg=BG)
        setup_theme(win)
        outer = tk.Frame(win, bg=BG)
        outer.pack(fill="both", expand=True, padx=24, pady=22)
        card, body = ui_card(outer, pad=16)
        ui_label(body, "播放设备已连接", F_H2, INK, CARD).pack(anchor="w")
        ui_label(body, f"{root} · {rec.get('model') or '播放设备'}",
                 F_SUB, INK2, CARD).pack(anchor="w", pady=(8, 0))
        ui_label(body, "工具不会自动改动 U 盘，需要你亲自点一下。",
                 F_FINE, INK3, CARD).pack(anchor="w", pady=(6, 0))
        card.pack(fill="both", expand=True)

        def close():
            self._notify_open = False
            win.destroy()

        def go_copy():
            close()
            self._open_copy_dialog()

        bar = tk.Frame(outer, bg=BG)
        bar.pack(fill="x", pady=(14, 0))
        ui_button(bar, "暂不处理", close, "quiet").pack(side="right")
        ui_button(bar, "换一批歌", go_copy, "link").pack(side="right", padx=(0, 8))
        win.protocol("WM_DELETE_WINDOW", close)

    def _open_diagnose(self):
        """只读诊断刻意不检查设备白名单：陌生人也能零风险试用，这是信任入口。"""
        if self._diag_win is not None and self._diag_win.winfo_exists():
            self._diag_win.lift()
            return
        root = self.root_var.get()
        if not root or not os.path.isdir(root):
            messagebox.showwarning("U 盘未就绪", "请先插上要诊断的 U 盘并选中盘符")
            return
        self._diag_win = DiagnoseDialog(self, root, self.recursive.get())
        self.status.set("只读诊断完成 · 未写入任何文件")

    def _open_about(self):
        if self._about_win is not None and self._about_win.winfo_exists():
            self._about_win.lift()
            return
        self._about_win = AboutDialog(self)

    def _open_copy_dialog(self):
        if self._copy_win is not None and self._copy_win.winfo_exists():
            self._copy_win.lift()
            return
        root = self.root_var.get()
        if not root or not os.path.isdir(root):
            messagebox.showwarning("U 盘未就绪", "请先插上播放设备")
            return
        if not self._require_headset(root):
            return
        self._copy_win = CopyDialog(self, root, self.cfg, self._after_copy)

    def _after_copy(self):
        """随机拷贝结束后刷新主界面（对话框关闭时回调）。"""
        self._copy_win = None
        self._rescan()
        self._update_device_status()

    def _execute(self):
        if self.busy:
            return
        root = self.root_var.get()
        if not self._require_headset(root):
            return
        if not self.plan:
            messagebox.showinfo("提示", "请先点「换一批」生成预览")
            return
        mode = self.mode.get()
        if mode == "rename" and not messagebox.askyesno(
                "提示：改名对多数固件无效",
                "很多播放设备按 FAT 目录项（拷贝顺序）读盘，不按文件名排序；\n"
                "这种情况下只改编号前缀完全不会改变播放顺序。\n"
                "建议先点「只读诊断」判定，再选「极速重排」或「清盘重写」。\n\n"
                "仍要继续「仅重命名」吗？"):
            return
        if mode == "fast" and self.recursive.get():
            messagebox.showerror("不支持", "极速重排只处理 U 盘根目录，请先取消勾选「包含子目录」")
            return
        gb = sum(p["size"] for p in self.plan) / 1024**3
        mode_desc = {
            "fast": "极速重排（零拷贝 · 秒级 · 不需要电脑备份）",
            "rewrite": "清盘重写（备份 → 删除 → 写回，搬运两遍数据）",
            "rename": "仅重命名（不删除文件）",
        }[mode]
        lines = [
            f"目标：{root}",
            f"音频文件：{len(self.plan)} 首 · {gb:.2f} GB",
            f"模式：{mode_desc}",
            f"文件名：{'001.flac 安全短名' if self.safe_names.get() else '保留中文歌名，仅换编号前缀'}",
        ]
        if mode == "fast":
            lines += [
                "",
                "不删除、不复制任何音频数据，只重排 FAT 目录项，通常数秒完成。",
                "数据全程留在 U 盘上，也不需要占用电脑硬盘做备份。",
                "首次使用请验证：安全弹出 → 设备断电重连 → 听第一首是否变了；",
                "若没变，点「一键还原」后改用「清盘重写」。",
            ]
        if mode == "rewrite":
            est = int(gb * 1024 * 2 / 60)     # 按保守吞吐估算，读+写各一遍
            lines += [
                "",
                f"按 {ASSUMED_MBPS:g} MB/s 保守估算，需搬运 {gb * 2:.1f} GB，预计约 {est} 分钟。",
                "（实际速度取决于你的 U 盘；执行时会显示实时速度与剩余时间。）",
                f"执行前会把这 {len(self.plan)} 首完整备份到：{BACKUP_ROOT}",
                "备份校验通过后才会删除 U 盘上的原文件；期间请勿拔出 U 盘。",
            ]
        lines += ["", "确认开始？"]
        if not messagebox.askyesno("二次确认", "\n".join(lines)):
            return
        plan, tracks, safe = list(self.plan), list(self.tracks), self.safe_names.get()
        def job():
            apply_all(root, mode, plan, tracks, safe, self._progress)
            extra = ""
            if mode == "fast" and MANIFEST.is_file():
                mm = json.loads(MANIFEST.read_text(encoding="utf-8"))
                if mm.get("verified") is False:
                    extra = "\n目录项顺序校验未通过，请点「一键还原」后改用「清盘重写」"
            return (f"洗牌完成：{len(plan)} 首{extra}\n"
                    "记得安全弹出 U 盘并让设备断电重连，再试听顺序。")
        self._run_bg(job)

    def _restore(self):
        if self.busy:
            return
        if not MANIFEST.is_file():
            messagebox.showinfo("提示", "还没有执行过洗牌，无需还原")
            return
        m = json.loads(MANIFEST.read_text(encoding="utf-8"))
        target = m.get("root") or self.root_var.get()
        if not os.path.isdir(target):
            messagebox.showwarning("U 盘未就绪",
                                   f"还原目标 {target} 当前不可用，请先插上播放设备")
            return
        if not self._require_headset(target):
            return
        if not messagebox.askyesno(
                "确认还原",
                f"把 {m['root']} 还原到 {m['created']} 洗牌之前的状态？\n"
                f"模式：{m['mode']} · 共 {len(m['tracks'])} 首"):
            return
        self._run_bg(lambda: restore(self._progress))


_DialogBase = tk.Toplevel if tk is not None else object


class DiagnoseDialog(_DialogBase):
    """只读诊断报告窗口：全程不写入任何文件。"""

    def __init__(self, parent, root: str, recursive: bool = False):
        super().__init__(parent)
        self.transient(parent)
        self.title("只读诊断")
        self.configure(bg=BG)
        setup_theme(self)
        self.geometry("720x540")
        self.minsize(600, 420)
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True, padx=22, pady=20)
        tk.Label(outer, text="只读诊断", font=F_H2, fg=INK, bg=BG,
                 anchor="w").pack(fill="x")
        tk.Label(outer, text="只读取目录与文件属性，没有创建、修改或删除任何文件。",
                 font=F_SUB, fg=INK2, bg=BG, anchor="w").pack(
                     fill="x", pady=(2, 12))
        body = tk.Frame(outer, bg=CARD, highlightbackground=LINE,
                        highlightthickness=1, bd=0)
        body.pack(fill="both", expand=True)
        inner = tk.Frame(body, bg=CARD)
        inner.pack(fill="both", expand=True, padx=10, pady=10)
        txt = tk.Text(inner, wrap="word", font=("Microsoft YaHei UI", 10),
                      bg=CARD, fg=INK, relief="flat", bd=0, padx=8, pady=8)
        sb = ttk.Scrollbar(inner, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)
        try:
            self.report = diagnose_text(diagnose(root, recursive))
        except Exception as exc:
            self.report = (f"诊断失败：{exc}\n\n"
                           "这仍然是一次只读操作，没有对 U 盘做任何写入。")
        txt.insert("1.0", self.report)
        txt.configure(state="disabled")
        bar = tk.Frame(outer, bg=BG)
        bar.pack(fill="x", pady=(12, 0))
        ui_button(bar, "关闭", self.destroy, "quiet").pack(side="right")
        ui_button(bar, "复制报告", self._copy, "link").pack(side="left")
        self.bind("<Escape>", lambda _: self.destroy())
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    def _copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.report)
        messagebox.showinfo("已复制", "报告已复制到剪贴板，可贴到论坛或 issue 里。", parent=self)


class AboutDialog(_DialogBase):
    """关于：一句引导语 + 赞赏码 + 版本。其余信息按需展开，不再堆文字。"""

    def __init__(self, parent):
        super().__init__(parent)
        self.transient(parent)
        self.title("关于")
        self.configure(bg=BG)
        setup_theme(self)
        self.geometry("420x540")
        self.resizable(False, False)
        self._notice = None
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True, padx=26, pady=22)

        tk.Label(outer, text="ShuffleStick", font=F_H2, fg=INK, bg=BG).pack()
        tk.Label(outer, text=f"v{APP_VERSION} · MIT 开源 · 完全离线",
                 font=F_FINE, fg=INK3, bg=BG).pack(pady=(2, 18))

        card, body = ui_card(outer, pad=22)
        tk.Label(body, text=DONATE_SLOGAN, font=F_H2, fg=INK, bg=CARD,
                 wraplength=320, justify="center").pack(pady=(4, 18))
        if DONATE_IMAGE.is_file():
            try:
                raw = tk.PhotoImage(file=str(DONATE_IMAGE))
                n = max(1, -(-raw.width() // 260), -(-raw.height() // 260))
                self._raw_img = raw
                self._img = raw.subsample(n, n) if n > 1 else raw
                tk.Label(body, image=self._img, bg=CARD, bd=0).pack()
                tk.Label(body, text="微信扫一扫 · 完全自愿",
                         font=F_SUB, fg=INK2, bg=CARD).pack(pady=(14, 2))
            except Exception:
                tk.Label(body, text="赞赏码图片无法读取",
                         font=F_SUB, fg=INK3, bg=CARD).pack()
        else:
            tk.Label(body, text="赞赏码图片未随包提供",
                     font=F_SUB, fg=INK3, bg=CARD).pack()
            tk.Label(body, text="软件功能不受影响",
                     font=F_FINE, fg=INK3, bg=CARD).pack(pady=(4, 2))
        card.pack(fill="x")

        self.notice_host = tk.Frame(outer, bg=BG)
        self.notice_host.pack(fill="x")
        bar = tk.Frame(outer, bg=BG)
        bar.pack(side="bottom", fill="x", pady=(16, 0))
        ui_button(bar, "关闭", self.destroy, "quiet").pack(side="right")
        ui_button(bar, "复制源码地址",
                  lambda: self._copy(source_urls()["primary"]), "quiet").pack(side="left")
        ui_button(bar, "使用须知", self._toggle_notice, "quiet").pack(
            side="left", padx=(0, 10))
        self.bind("<Escape>", lambda _: self.destroy())
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    def _toggle_notice(self):
        if self._notice is not None:
            self._notice.destroy()
            self._notice = None
            self.geometry("420x540")
            return
        self._notice = tk.Frame(self.notice_host, bg=BG)
        tk.Label(self._notice, text=DISCLAIMER, font=F_FINE, fg=INK2, bg=BG,
                 wraplength=350, justify="left", anchor="w").pack(
                     fill="x", pady=(14, 0))
        self._notice.pack(fill="x")
        self.update_idletasks()
        h = min(700, max(540, self.winfo_reqheight() + 20),
                self.winfo_screenheight() - 80)
        self.geometry(f"420x{h}")

    def _copy(self, text: str):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.status_text = None
        messagebox.showinfo("已复制", "源码地址已复制到剪贴板。", parent=self)


class SetupDialog(_DialogBase):
    """一次性引导：认识设备 → 选盘 → 绑定。完成后不再出现，也不占日常界面。"""

    STEPS = ("认识设备", "选择 U 盘", "确认绑定")

    def __init__(self, parent):
        super().__init__(parent)
        self.app = parent
        self.transient(parent)
        self.title("第一次使用")
        self.configure(bg=BG)
        setup_theme(self)
        self.geometry("500x420")
        self.resizable(False, False)
        self.protocol("WM_DELETE_WINDOW", self._close)
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True, padx=28, pady=26)
        self.steps_bar = tk.Frame(outer, bg=BG)
        self.steps_bar.pack(fill="x")
        self.body = tk.Frame(outer, bg=BG)
        self.body.pack(fill="both", expand=True, pady=(22, 0))
        self.bar = tk.Frame(outer, bg=BG)
        self.bar.pack(side="bottom", fill="x")
        self._show(0)

    def _close(self):
        self.app._setup_win = None
        self.destroy()

    def _clear(self):
        for w in (*self.body.winfo_children(), *self.bar.winfo_children(),
                  *self.steps_bar.winfo_children()):
            w.destroy()

    def _head(self, step, title, sub):
        row = tk.Frame(self.steps_bar, bg=BG)
        row.pack()
        for i, name in enumerate(self.STEPS):
            tk.Label(row, text=f"{i + 1}  {name}", font=F_FINE,
                     fg=ACCENT if i <= step else INK3, bg=BG).pack(
                         side="left", padx=(0, 16))
        tk.Label(self.body, text=title, font=("Microsoft YaHei UI", 16, "bold"),
                 fg=INK, bg=BG, anchor="w").pack(fill="x", pady=(18, 0))
        tk.Label(self.body, text=sub, font=F_BODY, fg=INK2, bg=BG,
                 wraplength=430, justify="left", anchor="w").pack(
                     fill="x", pady=(10, 0))

    def _show(self, step):
        self._clear()
        self._head(step, *({
            0: ("三步，之后就不用管了",
                "很多播放器不按文件名读歌，而是按 U 盘里的写入顺序。\n"
                "这个工具帮你换一批歌、打乱顺序。"),
            1: ("插上设备，选中盘符", "插好要放歌的 U 盘，从下拉框里选中它。"),
            2: ("确认这是播放设备", "绑定后只有这块盘允许写入，其它 U 盘一律忽略。"),
        }[step]))
        if step == 0:
            card, c = ui_card(self.body, pad=14)
            tk.Label(c, text="绑定前不会改动 U 盘上的任何文件。", font=F_SUB,
                     fg=INK2, bg=CARD, anchor="w", wraplength=390,
                     justify="left").pack(fill="x")
            card.pack(fill="x", pady=(20, 0))
            ui_button(self.bar, "开始", lambda: self._show(1)).pack(side="right")
            ui_button(self.bar, "以后再说", self._close, "quiet").pack(side="left")
        elif step == 1:
            row = tk.Frame(self.body, bg=BG)
            row.pack(fill="x", pady=(20, 0))
            cb = ttk.Combobox(row, textvariable=self.app.root_var,
                              values=list_drives(), width=8, state="readonly")
            cb.pack(side="left")
            ui_button(row, "刷新", self._app_refresh, "quiet").pack(
                side="left", padx=(10, 0))
            self.dev_info = tk.Label(self.body, text="", font=F_SUB, fg=INK2,
                                     bg=BG, anchor="w", justify="left",
                                     wraplength=430)
            self.dev_info.pack(fill="x", pady=(14, 0))
            self._info()
            ui_button(self.bar, "下一步", lambda: self._show(2)).pack(side="right")
            ui_button(self.bar, "上一步", lambda: self._show(0), "quiet").pack(
                side="left")
        else:
            card, c = ui_card(self.body, pad=16)
            self.confirm = tk.Label(c, text="", font=F_BODY, fg=INK, bg=CARD,
                                    anchor="w", justify="left", wraplength=390)
            self.confirm.pack(fill="x")
            card.pack(fill="x", pady=(20, 0))
            self._confirm_text()
            ui_button(self.bar, "完成设置", self._finish).pack(side="right")
            ui_button(self.bar, "上一步", lambda: self._show(1), "quiet").pack(
                side="left")

    def _app_refresh(self):
        self.app._refresh_drives()
        self._info()

    def _info(self):
        root = self.app.root_var.get()
        if not root or not os.path.isdir(root):
            self.dev_info.configure(text="未检测到可移动 U 盘，插好后点「刷新」。")
            return
        fp = device_fingerprint(root)
        self.dev_info.configure(
            text=(f"{root} · {volume_info(root)}\n"
                  f"卷序列号 {fp['serial'] or '?'} · 当前 {fp['audio_count']} 首音频"))

    def _confirm_text(self):
        root = self.app.root_var.get()
        if not root or not os.path.isdir(root):
            self.confirm.configure(text="设备未就绪，请返回上一步重新选择盘符。")
            return
        fp = device_fingerprint(root)
        self.confirm.configure(
            text=(f"{root} · {volume_info(root)}\n"
                  f"容量 {fp['total'] / 1024**3:.1f} GB · {fp['fs']} · "
                  f"{fp['audio_count']} 首音频\n\n"
                  "请确认这台设备就是你要放歌的那台，不是存文件的普通 U 盘。"))

    def _finish(self):
        root = self.app.root_var.get()
        if not root or not os.path.isdir(root):
            messagebox.showwarning("设备未就绪", "请先插上播放设备并选中盘符",
                                   parent=self)
            return
        try:
            bind_headset(root, self.app.cfg, model=usb_device_model(root))
        except Exception as exc:
            messagebox.showerror("绑定失败", str(exc), parent=self)
            return
        self.app.cfg["onboarded"] = True
        save_config(self.app.cfg)
        self.app._update_device_status()
        self.app.status.set("已绑定播放设备 · 可以开始换歌了")
        self._close()


class SettingsDialog(_DialogBase):
    """全部低频参数集中在这里，主界面一个技术选项都不留。"""

    def __init__(self, parent):
        super().__init__(parent)
        self.app = parent
        self.transient(parent)
        self.title("设置")
        self.configure(bg=BG)
        setup_theme(self)
        self.geometry("540x640")
        self.minsize(500, 600)
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True, padx=26, pady=22)
        # 底部固定区先占位，内容再多也不会把「完成」挤出窗口
        bar = tk.Frame(outer, bg=BG)
        bar.pack(side="bottom", fill="x", pady=(12, 0))
        ui_button(bar, "完成", self._close, "quiet").pack(side="right")
        tk.Label(outer, text="设置", font=F_H2, fg=INK, bg=BG,
                 anchor="w").pack(fill="x")
        tk.Label(outer, text="改完自动保存；日常使用不需要动这里。",
                 font=F_FINE, fg=INK3, bg=BG, anchor="w").pack(
                     fill="x", pady=(2, 14))

        self.src_var = tk.StringVar(value=str(self.app.cfg.get("source_dir") or ""))
        self.cap_var = tk.StringVar(
            value=f"{int(self.app.cfg.get('capacity_mb', 2048)) / 1024:g}")

        self._group(outer, "重排方式")
        for text, val in (("极速重排 · 秒级，不搬运文件（推荐）", "fast"),
                          ("清盘重写 · 兼容兜底，较慢", "rewrite"),
                          ("仅重命名 · 多数设备无效", "rename")):
            ttk.Radiobutton(outer, text=text, variable=self.app.mode,
                            value=val, command=self._save).pack(
                                anchor="w", pady=2, padx=8)

        self._group(outer, "文件与扫描")
        ttk.Checkbutton(outer, text="改用 001.flac 安全短名（默认保留中文歌名）",
                        variable=self.app.safe_names,
                        command=self._on_scan).pack(anchor="w", pady=2, padx=8)
        ttk.Checkbutton(outer, text="洗牌扫描时包含子目录",
                        variable=self.app.recursive,
                        command=self._on_scan).pack(anchor="w", pady=2, padx=8)
        row = tk.Frame(outer, bg=BG)
        row.pack(fill="x", pady=(6, 0), padx=8)
        tk.Label(row, text="随机种子", font=F_SUB, fg=INK2, bg=BG,
                 width=10, anchor="w").pack(side="left")
        ttk.Entry(row, textvariable=self.app.seed, width=18).pack(side="left")
        tk.Label(row, text="留空即每次随机", font=F_FINE, fg=INK3,
                 bg=BG).pack(side="left", padx=(8, 0))

        self._group(outer, "插盘提醒")
        ttk.Checkbutton(outer, text="插入设备时提醒我（只提醒，不自动写盘）",
                        variable=self.app.auto,
                        command=self._toggle_auto).pack(anchor="w", pady=2, padx=8)
        row = tk.Frame(outer, bg=BG)
        row.pack(fill="x", pady=(6, 0), padx=8)
        tk.Label(row, text="提醒冷却", font=F_SUB, fg=INK2, bg=BG,
                 width=10, anchor="w").pack(side="left")
        ttk.Spinbox(row, from_=0, to=240, width=5,
                    textvariable=self.app.cooldown_var).pack(side="left")
        tk.Label(row, text="分钟 · 需保持窗口开启", font=F_FINE, fg=INK3,
                 bg=BG).pack(side="left", padx=(8, 0))

        self._group(outer, "音频库（随机拷贝用）")
        row = tk.Frame(outer, bg=BG)
        row.pack(fill="x", pady=2, padx=8)
        ttk.Entry(row, textvariable=self.src_var, width=38).pack(side="left")
        ui_button(row, "浏览", self._browse, "link").pack(side="left", padx=(8, 0))
        row = tk.Frame(outer, bg=BG)
        row.pack(fill="x", pady=(8, 0), padx=8)
        tk.Label(row, text="每批容量", font=F_SUB, fg=INK2, bg=BG,
                 width=10, anchor="w").pack(side="left")
        ttk.Spinbox(row, from_=0.1, to=64, increment=0.5, width=6,
                    textvariable=self.cap_var,
                    command=self._save).pack(side="left")
        tk.Label(row, text="GB", font=F_FINE, fg=INK3, bg=BG).pack(
            side="left", padx=(8, 0))

        self.protocol("WM_DELETE_WINDOW", self._close)
        self.bind("<Escape>", lambda _: self._close())

    @staticmethod
    def _group(master, text):
        line = tk.Frame(master, bg=LINE, height=1)
        line.pack(fill="x", pady=(10, 6))
        tk.Label(master, text=text, font=F_FINE, fg=INK3, bg=BG,
                 anchor="w").pack(fill="x")

    def _on_scan(self):
        self._save()
        self.app._rescan()

    def _toggle_auto(self):
        self.app._toggle_auto()
        self._save()

    def _browse(self):
        d = filedialog.askdirectory(parent=self, title="选择本地音频库目录")
        if d:
            self.src_var.set(d)
            self._save()

    def _save(self, *_):
        cfg = self.app.cfg
        cfg["shuffle_mode"] = self.app.mode.get()
        cfg["safe_names"] = bool(self.app.safe_names.get())
        cfg["scan_recursive"] = bool(self.app.recursive.get())
        cfg["seed"] = self.app.seed.get()
        cfg["remind_on_insert"] = bool(self.app.auto.get())
        cfg["source_dir"] = self.src_var.get()
        try:
            cfg["capacity_mb"] = max(64, int(float(self.cap_var.get()) * 1024))
        except (TypeError, ValueError):
            pass
        save_config(cfg)

    def _close(self):
        self._save()
        self.app._settings_win = None
        self.destroy()


class CopyDialog(_DialogBase):
    """本地音频库 → 播放设备：按容量随机挑选 + 拷贝即乱序。

    所有写操作都要经过：设备白名单 → 选择替换/追加 → 二次确认 → 后台执行。
    源目录、容量、上一批名单都持久化，下次打开直接沿用。
    """

    def __init__(self, parent, root: str, cfg: dict, on_close):
        super().__init__(parent)
        self.app = parent
        self.root = root
        self.cfg = cfg
        self.on_close = on_close
        self.q: queue.Queue = queue.Queue()
        self.busy = False
        self._closed = False
        self.library: list[SourceTrack] = []
        self.picked: list[SourceTrack] = []
        self.seed = ""
        self.title("随机拷贝 · 本地音频库 → 播放设备")
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = 760, min(640, max(520, sh - 140))
        self.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 6)}")
        self.minsize(700, 520)
        self.transient(parent)
        self.protocol("WM_DELETE_WINDOW", self._close)

        self.src_var = tk.StringVar(value=str(cfg.get("source_dir") or ""))
        self.cap_var = tk.StringVar(value=f"{int(cfg.get('capacity_mb', 2048)) / 1024:g}")
        self.rec_var = tk.BooleanVar(value=bool(cfg.get("recursive", True)))
        self.avoid_var = tk.BooleanVar(value=bool(cfg.get("avoid_repeat", True)))
        self.status = tk.StringVar(value="就绪 · 选择音频库目录后生成随机预览")
        self.summary = tk.StringVar(value="尚未生成预览")

        self._build()
        self.after(80, self._pump)
        if self.src_var.get():
            self._scan_library()

    def _build(self):
        self.configure(bg=BG)
        setup_theme(self)
        outer = tk.Frame(self, bg=BG)
        outer.pack(fill="both", expand=True, padx=22, pady=18)

        # 底部固定区先占位，保证按钮不会被挤出窗口
        foot = tk.Frame(outer, bg=BG)
        tk.Label(foot, textvariable=self.status, font=F_FINE, fg=INK3,
                 bg=BG, anchor="w").pack(side="left")
        foot.pack(side="bottom", fill="x", pady=(6, 0))
        self.pbar = ttk.Progressbar(outer, mode="determinate", maximum=100)
        self.pbar.pack(side="bottom", fill="x", pady=(6, 0))
        act = tk.Frame(outer, bg=BG)
        self.go_btn = ui_button(act, "开始拷贝", self._start)
        self.go_btn.pack(side="left")
        self.shuffle_btn = ui_button(act, "换一批（仅预览）",
                                     self._reshuffle, "link")
        self.shuffle_btn.pack(side="left", padx=(12, 0))
        ui_button(act, "关闭", self._close, "quiet").pack(side="right")
        act.pack(side="bottom", fill="x", pady=(10, 0))
        tk.Label(outer, textvariable=self.summary, font=F_SUB, fg=INK2,
                 bg=BG, anchor="w").pack(side="bottom", fill="x", pady=(8, 0))

        fp = device_fingerprint(self.root)
        rec = match_headset(fp, self.cfg) or {}
        free = shutil.disk_usage(self.root).free
        card, dev = ui_card(outer, pad=14)
        tk.Label(dev, justify="left", anchor="w", font=F_SUB, fg=INK, bg=CARD,
                 text=(f"{rec.get('model') or '播放设备'} · {self.root} / {fp['serial']}\n"
                       f"当前 {fp['audio_count']} 首音频 · 可用 {free / 1024**3:.1f} GB")
                 ).pack(anchor="w")
        card.pack(fill="x", pady=(0, 6))

        self._section(outer, "本地音频库 · 下次打开自动记住")
        r = tk.Frame(outer, bg=BG)
        r.pack(fill="x", pady=(6, 0))
        ttk.Entry(r, textvariable=self.src_var).pack(side="left", fill="x", expand=True)
        self.browse_btn = ttk.Button(r, text="浏览", command=self._browse)
        self.browse_btn.pack(side="left", padx=(8, 0))
        ttk.Button(r, text="扫描", command=self._scan_library).pack(
            side="left", padx=(8, 0))

        self._section(outer, "筛选条件")
        o = tk.Frame(outer, bg=BG)
        o.pack(fill="x", pady=(6, 0))
        tk.Label(o, text="容量上限", font=F_SUB, fg=INK2, bg=BG).pack(side="left")
        ttk.Entry(o, textvariable=self.cap_var, width=8).pack(side="left", padx=(8, 4))
        tk.Label(o, text="GB", font=F_FINE, fg=INK3, bg=BG).pack(side="left")
        ttk.Checkbutton(o, text="包含子目录", variable=self.rec_var,
                        command=self._on_param).pack(side="left", padx=(18, 0))
        ttk.Checkbutton(o, text="尽量避开上一批", variable=self.avoid_var,
                        command=self._on_param).pack(side="left", padx=(14, 0))

        self._section(outer, "本次将拷入 · 顺序即播放顺序")
        pv = tk.Frame(outer, bg=CARD, highlightbackground=LINE,
                      highlightthickness=1, bd=0)
        inner = tk.Frame(pv, bg=CARD)
        inner.pack(fill="both", expand=True, padx=10, pady=10)
        cols = ("no", "name", "mb")
        tv = ttk.Treeview(inner, columns=cols, show="headings")
        tv.heading("no", text="#")
        tv.column("no", width=50, anchor="center", stretch=False)
        tv.heading("name", text="文件名（保留中文歌名，仅换编号）")
        tv.column("name", width=380, anchor="w")
        tv.heading("mb", text="MB")
        tv.column("mb", width=80, anchor="e", stretch=False)
        sb = ttk.Scrollbar(inner, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb.set)
        tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tv = tv
        pv.pack(side="top", fill="both", expand=True, pady=(6, 0))

    @staticmethod
    def _section(master, text):
        line = tk.Frame(master, bg=LINE, height=1)
        line.pack(fill="x", pady=(12, 6))
        tk.Label(master, text=text, font=F_FINE, fg=INK3, bg=BG,
                 anchor="w").pack(fill="x")

    # -- 偏好 ---------------------------------------------------------------
    def _save_prefs(self):
        self.cfg["source_dir"] = self.src_var.get().strip()
        try:
            self.cfg["capacity_mb"] = max(1, int(float(self.cap_var.get()) * 1024))
        except ValueError:
            pass
        self.cfg["recursive"] = bool(self.rec_var.get())
        self.cfg["avoid_repeat"] = bool(self.avoid_var.get())
        save_config(self.cfg)

    def _browse(self):
        d = filedialog.askdirectory(title="选择本地音频库目录",
                                    initialdir=self.src_var.get() or None,
                                    parent=self)
        if d:
            self.src_var.set(os.path.normpath(d))
            self._save_prefs()
            self._scan_library()

    def _on_param(self):
        self._save_prefs()
        self._scan_library()

    # -- 扫描与预览（只读） -------------------------------------------------
    def _scan_library(self):
        src = self.src_var.get().strip()
        if not src or not os.path.isdir(src):
            self.library = []
            self._render([])
            self.summary.set("请选择有效的音频库目录（点「浏览…」）")
            return
        self._save_prefs()
        self.status.set("正在扫描音频库…")
        # Tk 变量只能在主线程读：先取值再交给后台线程，避免跨线程访问异常
        recursive = bool(self.rec_var.get())

        def work():
            try:
                self.q.put(("lib", scan_library(src, recursive)))
            except Exception as exc:
                self.q.put(("liberr", str(exc)))

        threading.Thread(target=work, daemon=True).start()

    def _reshuffle(self):
        if not self.library:
            messagebox.showinfo("提示", "请先选择音频库目录", parent=self)
            return
        self.seed = str(random.random())
        self._preview()

    def _preview(self):
        try:
            gb = float(self.cap_var.get())
            if gb <= 0:
                raise ValueError
        except ValueError:
            gb = 2.0
            self.cap_var.set("2")
        cap = int(gb * 1024**3)
        free = shutil.disk_usage(self.root).free
        safe_cap = max(0, free - 256 * 1024**2)
        capped = cap > safe_cap
        cap = min(cap, safe_cap)
        self.picked = pick_tracks(self.library, cap,
                                  self.cfg.get("last_batch", []),
                                  bool(self.avoid_var.get()), self.seed)
        self._render(self.picked)
        total = sum(t.size for t in self.picked)
        secs = estimate_seconds(total)
        self.summary.set(
            f"将拷贝 {len(self.picked)} 首 / {total / 1024**3:.2f} GB"
            f"{' · 已按剩余空间自动调低' if capped else ''} · "
            f"按 {ASSUMED_MBPS:g} MB/s 保守估算 {secs // 60} 分 {secs % 60} 秒 · 库中共 {len(self.library)} 首")
        self.status.set("预览已生成 · 尚未写入 U 盘")

    def _render(self, items):
        self.tv.delete(*self.tv.get_children())
        for i, t in enumerate(items[:300], 1):
            self.tv.insert("", "end", values=(f"{i:03d}", t.name, f"{t.mb:.1f}"))
        if len(items) > 300:
            self.tv.insert("", "end",
                           values=("…", f"还有 {len(items) - 300} 首未列出", ""))

    # -- 执行 ---------------------------------------------------------------
    def _start(self):
        if self.busy or not self.picked:
            if not self.picked:
                messagebox.showinfo("提示", "请先选目录并生成预览", parent=self)
            return
        fp = device_fingerprint(self.root)
        rec = match_headset(fp, self.cfg)
        if not rec:
            messagebox.showerror("设备校验失败",
                                 "当前 U 盘不是已绑定的播放设备，已阻止写入。", parent=self)
            return
        old = _audio_entries(Path(self.root))
        total = sum(t.size for t in self.picked)
        choice = messagebox.askyesnocancel(
            "选择写入方式",
            f"U 盘现有 {len(old)} 首音频，本次将写入 {len(self.picked)} 首。\n\n"
            "【是】替换整批：写入并校验新歌后，删除现有音频\n"
            "　　　（旧歌不备份到电脑，删除后无法「一键还原」）\n"
            "【否】追加：保留现有音频，新歌接在后面\n"
            "【取消】什么都不做\n\n请选择：", parent=self)
        if choice is None:
            return
        action = "replace" if choice else "append"
        secs = estimate_seconds(total)
        desc = (f"替换整批（删除现有 {len(old)} 首）" if action == "replace"
                else "追加（不删任何文件）")
        if not messagebox.askyesno(
                "最后确认 · 即将写入 U 盘",
                f"目标：{self.root} · {rec.get('model') or '播放设备'} / {fp['serial']}\n"
                f"源目录：{self.src_var.get()}\n"
                f"动作：{desc}\n"
                f"本次：{len(self.picked)} 首 / {total / 1024**3:.2f} GB\n\n"
                f"按 {ASSUMED_MBPS:g} MB/s 保守估算，预计 {secs // 60} 分 {secs % 60} 秒；"
                "期间请勿拔盘或关窗口。\n\n确认开始？", parent=self):
            return
        self._set_busy(True)
        self.pbar["value"] = 0
        picked = list(self.picked)

        def progress(done, total_n, text):
            self.q.put(("progress", (done, total_n, text)))

        def worker():
            try:
                with keep_awake():
                    res = copy_shuffled(self.root, picked, action, progress, False)
                self.q.put(("done", (True, res)))
            except Exception as exc:
                log(f"随机拷贝失败：{exc}")
                self.q.put(("done", (False, str(exc))))

        threading.Thread(target=worker, daemon=True).start()

    def _set_busy(self, busy):
        self.busy = busy
        state = "disabled" if busy else "normal"
        for b in (self.go_btn, self.shuffle_btn, self.browse_btn):
            b.configure(state=state)

    def _pump(self):
        if self._closed:
            return
        try:
            while True:
                kind, payload = self.q.get_nowait()
                if kind == "lib":
                    self.library = payload
                    self._preview()
                elif kind == "liberr":
                    self.status.set(f"扫描失败：{payload}")
                    messagebox.showerror("扫描失败", payload, parent=self)
                elif kind == "progress":
                    d, t, txt = payload
                    self.pbar["value"] = max(0, min(100, 100 * d / max(1, t)))
                    self.status.set(txt)
                elif kind == "done":
                    ok, res = payload
                    self._set_busy(False)
                    if ok:
                        self.cfg["last_batch"] = [t.key for t in self.picked]
                        self._save_prefs()
                        self.pbar["value"] = 100
                        warn = ("" if res["verified"] else
                                "\n目录项顺序校验未通过，请试听确认；必要时改用「清盘重写」。")
                        self.status.set(f"完成：{res['count']} 首 / {res['bytes'] / 1024**3:.2f} GB")
                        messagebox.showinfo(
                            "随机拷贝完成",
                            f"已写入 {res['count']} 首 / {res['bytes'] / 1024**3:.2f} GB，"
                            f"用时 {int(res['seconds'] // 60)} 分 {int(res['seconds'] % 60)} 秒。\n"
                            f"方式：{'替换（删除旧歌 %d 首）' % res['removed'] if res['action'] == 'replace' else '追加（旧歌保留）'}"
                            f"{warn}\n\n关闭本窗口后主界面会刷新；"
                            "安全弹出 U 盘并让设备断电重连再试听。", parent=self)
                    else:
                        self.status.set("拷贝失败（已自动回滚）")
                        messagebox.showerror(
                            "随机拷贝失败",
                            f"{res}\n\n已尽量回滚，U 盘应回到执行前状态；可检查后再试。",
                            parent=self)
        except queue.Empty:
            pass
        if not self._closed:
            self.after(80, self._pump)

    def _close(self):
        if self.busy and not messagebox.askyesno(
                "任务进行中", "拷贝尚未完成，强制退出可能让 U 盘停在半途。\n确定退出吗？",
                parent=self):
            return
        cb, self.on_close = self.on_close, None
        self._closed = True
        self.destroy()
        if cb:
            cb()


# --------------------------------------------------------------------------- 自检

def selftest_diagnose() -> int:
    """只读诊断：三种首曲判定、报告文本、纯只读性、赞赏引导语。"""
    import tempfile

    print("=== 只读诊断自检 ===")
    with tempfile.TemporaryDirectory(prefix="shuf_diag_") as td:
        root = Path(td)
        # 创建顺序 / 名字序 / 时间序 的首曲故意各不相同
        spec = [("b_dir.flac", 300), ("d_time.flac", 100),
                ("a_name.flac", 400), ("c_other.flac", 200)]
        for name, ts in spec:
            p = root / name
            p.write_bytes(b"x" * 1024)
            os.utime(p, (ts * 1000, ts * 1000))
        before = {p.name: (p.stat().st_size, p.stat().st_mtime)
                  for p in root.iterdir()}

        # 纯逻辑：喂入确定的目录项顺序，精确验证三种规则
        fake = [Track(n, 1024, float(ts), False, ".flac", i)
                for i, (n, ts) in enumerate(spec)]
        fr = first_by_rules(fake)
        assert fr["A 文件名字典序"] == "a_name.flac", fr
        assert fr["B FAT 目录项 / 拷贝顺序"] == "b_dir.flac", fr
        assert fr["C 修改时间升序"] == "d_time.flac", fr
        assert len(set(fr.values())) == 3
        print("  三种首曲判定（纯函数）：", fr)

        # 集成：真实文件系统只读扫描（NTFS 下 A/B 可能相同，不假设 distinct）
        d = diagnose(td)
        assert d["ok"] and d["audio_count"] == 4 and len(d["first"]) == 3, d
        assert d["distinct"] >= 1, d["first"]
        print("  真实目录扫描：distinct =", d["distinct"], "| first =", d["first"])

        text = diagnose_text(d)
        for key in ("只读诊断报告", "没有创建、修改或删除任何文件",
                    "A 文件名字典序", "B FAT 目录项", "C 修改时间",
                    "听第一首", "极速重排"):
            assert key in text, key
        print("  报告文本 OK · %d 字" % len(text))

        after = {p.name: (p.stat().st_size, p.stat().st_mtime)
                 for p in root.iterdir()}
        assert before == after, "诊断过程改动了文件！"
        print("  纯只读校验 OK（文件名 / 大小 / mtime 全部未变）")

        empty = tempfile.mkdtemp(prefix="shuf_diag_empty_")
        try:
            d2 = diagnose(empty)
            assert not d2["ok"] and d2["distinct"] == 0
            assert "未找到音频文件" in diagnose_text(d2)
            print("  空盘分支 OK")
        finally:
            os.rmdir(empty)

    assert DONATE_SLOGAN and len(DONATE_SLOGAN) <= 18
    print("  赞赏引导语 OK：", DONATE_SLOGAN)
    print("=== DIAGNOSE OK ===")
    return 0


def selftest() -> int:
    """不弹窗、不写 U 盘，仅验证扫描与计划生成逻辑。"""
    print("=== 自检（只读，不会改动 U 盘）===")
    drives = list_drives()
    print("候选盘：", drives)
    root = preferred_drive(drives)
    if not root:
        print("未检测到可移动 U 盘（设备可能正脱离 USB 独立播放）。")
        print("在线扫描部分已跳过；核心逻辑请用 --selftest-copy / --selftest-write 验证。")
        return 0
    print("目标：", root, "|", volume_info(root), "| driveType =", drive_type(root[0]))
    print("卷序列号（自动洗牌绑定用）：", volume_serial(root))
    tracks = scan(root)
    print(f"音频文件数：{len(tracks)}")
    print("目录项顺序前 6：")
    for t in tracks[:6]:
        print(f"  {t.dir_index:03d}  {t.orig_name}  ({t.size / 1024**2:.1f} MB, ro={t.readonly})")
    print("\n三种可能排序规则的第一首（用来判定设备到底按哪种读）：")
    by_name = sorted(tracks, key=lambda t: t.orig_name)
    by_time = sorted(tracks, key=lambda t: t.mtime)
    print(f"  A 文件名字典序 → {by_name[0].orig_name}")
    print(f"  B 目录项/拷贝序 → {tracks[0].orig_name}")
    print(f"  C 修改时间升序 → {by_time[0].orig_name}")
    if len({by_name[0].orig_name, tracks[0].orig_name, by_time[0].orig_name}) > 1:
        print("  → 三者首曲不同：戴上设备听第一首即可判定规则，无需拆机或猜。")

    order = make_order(tracks)
    plan = build_plan(order, False)
    print("洗牌后前 6（保留歌名）：")
    for p in plan[:6]:
        print(f"  {p['seq']:03d}  {p['dst']}")
    plan2 = build_plan(order, True)
    print("洗牌后前 6（安全短名）：")
    for p in plan2[:6]:
        print(f"  {p['seq']:03d}  {p['dst']}")
    assert len({p["dst"] for p in plan}) == len(plan), "目标名冲突"
    assert len({p["dst"] for p in plan2}) == len(plan2), "目标名冲突"
    assert [p["mtime"] for p in plan] == sorted(p["mtime"] for p in plan), "时间戳顺序错误"
    print("=== 自检通过，U 盘未被改动 ===")
    return 0


def selftest_write() -> int:
    """在临时目录里跑完整写入/还原流程，绝不触碰 U 盘。"""
    import tempfile
    global MANIFEST, BACKUP_ROOT, safe_target_root
    print("=== 写入流程自测（临时目录，不碰 U 盘）===")
    with tempfile.TemporaryDirectory(prefix="shuf_sw_") as td:
        tmp = Path(td)
        root = tmp / "fake_u"
        root.mkdir()
        (root / "System Volume Information").mkdir()
        (root / "readme.txt").write_text("keep me", encoding="utf-8")
        originals = [f"{i:02d}_song{i}.mp3" for i in range(1, 7)]

        old_manifest, old_backup, old_guard = MANIFEST, BACKUP_ROOT, safe_target_root
        MANIFEST, BACKUP_ROOT, safe_target_root = tmp / "manifest.json", tmp / "backup", lambda r: None
        quiet = lambda *a, **k: None
        try:
            for mode in ("rename", "rewrite", "fast"):
                for p in list(root.iterdir()):
                    if p.is_file() and p.suffix.lower() in AUDIO_EXTS:
                        clear_readonly(p)
                        p.unlink()
                for i, name in enumerate(originals, start=1):
                    (root / name).write_bytes(bytes([i]) * 512)

                tracks = scan(str(root))
                assert len(tracks) == 6, f"{mode}: 扫描数不对"
                plan = build_plan(make_order(tracks, seed="42"), False)
                apply_all(str(root), mode, plan, tracks, False, quiet)

                got = sorted(p.name for p in root.iterdir() if p.suffix.lower() in AUDIO_EXTS)
                assert got == sorted(p["dst"] for p in plan), f"{mode}: 目标名不符 {got}"
                files = [root / p["dst"] for p in plan]
                by_time = sorted(files, key=lambda p: p.stat().st_mtime)
                assert [p.name for p in by_time] == [p.name for p in files], f"{mode}: 时间戳顺序不一致"
                assert (root / "readme.txt").read_text(encoding="utf-8") == "keep me", "误删非音频文件"
                print(f"  [{mode}] 洗牌 OK · 6 首 · 名字序/时间序一致 · 非音频文件保留")

                res = restore(quiet)
                names = sorted(p.name for p in root.iterdir() if p.suffix.lower() in AUDIO_EXTS)
                assert names == originals, f"{mode}: 还原不符 {names}"
                print(f"  [{mode}] 还原 OK · {res}")
                if mode == "rewrite":
                    cur = Path(json.loads(MANIFEST.read_text(encoding="utf-8"))["backup_dir"])
                    rotate_backups(keep=1)
                    assert cur.is_dir(), "备份轮转误删了当前还原清单指向的备份"
                    print(f"  [{mode}] 备份轮转 OK · 当前备份受保护")
        finally:
            MANIFEST, BACKUP_ROOT, safe_target_root = old_manifest, old_backup, old_guard
    print("=== 写入流程自测通过，U 盘未被改动 ===")
    return 0


def selftest_auto() -> int:
    """自动洗牌边沿/冷却/并发决策的纯逻辑测试，不碰 U 盘。"""
    print("=== 自动洗牌决策自测（不碰 U 盘）===")
    cases = [
        ((False, True, False, 9999, 30), "run",      "首次插入"),
        ((True,  True, False, 9999, 30), "none",     "盘一直插着"),
        ((False, False, False, 9999, 30), "none",    "盘未插入"),
        ((True,  False, False, 9999, 30), "none",    "拔出边沿"),
        ((False, True, True, 9999, 30), "busy",      "忙碌中插入"),
        ((False, True, False, 60, 30), "cooldown",   "冷却期内"),
        ((False, True, False, 1800, 30), "run",      "刚好满冷却"),
        ((False, True, False, 60, 0), "run",         "冷却设为0"),
    ]
    for args, want, label in cases:
        got = auto_decision(*args)
        assert got == want, f"{label}: 期望 {want}，实际 {got}"
        print(f"  {label:<12} → {got}")
    print("=== 自动洗牌决策自测通过 ===")
    return 0


def fat_probe(root: str = "E:\\") -> int:
    """
    真实 FAT 盘探针：验证「全量移出 → 按新序移回」能否改变目录项线性顺序。
    只在盘上新建 _SWPROBE_ 子目录并写 6 个 1 KB 测试文件，结束必清理。
    """
    import shutil as _sh
    rootp = Path(root)
    d, hold = rootp / "_SWPROBE_", rootp / "_SWPROBE_" / "_HOLD_"
    print(f"=== FAT 目录项顺序探针（{root}，仅写 6 KB 测试文件）===")
    if not rootp.is_dir():
        print("盘符不可用")
        return 1
    try:
        assert d.name == "_SWPROBE_"
        _sh.rmtree(d, ignore_errors=True)
        d.mkdir(); hold.mkdir()
        orig = [f"{i:02d}_probe.mp3" for i in range(1, 7)]
        for n in orig:
            (d / n).write_bytes(b"x" * 1024)
        before = [e.name for e in os.scandir(d) if e.is_file()]
        for n in before:
            (d / n).rename(hold / n)
        newnames = [f"{i:02d}_new.mp3" for i in (6, 4, 1, 5, 2, 3)]
        for old, new in zip(before, newnames):
            (hold / old).rename(d / new)
        after = [e.name for e in os.scandir(d) if e.is_file()]
        print("移出前：", before)
        print("移回序：", newnames)
        print("移回后：", after)
        ok = after == newnames
        print("结论：", "目录项顺序跟随 move → 极速重排可用" if ok
              else "目录项按文件名排序（可能不是 FAT）→ 请用清盘重写")
        return 0 if ok else 1
    finally:
        _sh.rmtree(d, ignore_errors=True)
        print("探针已清理：", not d.exists())


def selftest_copy() -> int:
    """临时目录里跑完整随机拷贝流程，不碰真实 U 盘、配置与日志。"""
    import tempfile
    import traceback
    tmp = Path(tempfile.mkdtemp(prefix="shuf_copy_"))
    g = globals()
    saved = {k: g[k] for k in ("CONFIG", "MANIFEST", "DATA", "LOG_ROOT", "log")}
    prog = lambda d, t, txt: None
    try:
        g["CONFIG"] = tmp / "config.json"
        g["MANIFEST"] = tmp / "last_manifest.json"
        g["DATA"] = tmp
        g["LOG_ROOT"] = tmp / "logs"
        g["LOG_ROOT"].mkdir(exist_ok=True)
        g["log"] = lambda *a, **k: None
        print("=== 随机拷贝自检（全在临时目录，不碰 U 盘）===")

        cfg = dict(DEFAULT_CONFIG)
        cfg.update({"source_dir": "D:/音乐库", "capacity_mb": 3072,
                    "last_batch": ["a/x.flac"]})
        save_config(cfg)
        r = load_config()
        assert r["source_dir"] == "D:/音乐库" and r["capacity_mb"] == 3072
        print("  [1] 配置持久化 OK（源目录 / 容量 / 上一批自动记住）")

        wl = [{"serial": "A1B2C3D4", "total": 32_000_000_000, "model": "TEST UDISK"}]
        c = {"device_whitelist": wl}
        assert match_headset({"serial": "a1b2c3d4", "total": 32_000_000_000}, c)
        assert not match_headset({"serial": "DEADBEEF", "total": 32_000_000_000}, c)
        assert not match_headset({"serial": "A1B2C3D4", "total": 8_000_000_000}, c)
        print("  [2] 设备白名单 OK（别的盘 / 容量不符一律拒绝）")

        lib_dir = tmp / "lib"
        (lib_dir / "sub").mkdir(parents=True)
        for i in range(24):
            p = (lib_dir / "sub" if i % 2 else lib_dir) / f"歌曲{i:02d}.flac"
            p.write_bytes(b"x" * (64 * 1024 * (i + 1)))
        (lib_dir / "封面.jpg").write_bytes(b"not audio")
        lib = scan_library(str(lib_dir), True)
        flat = scan_library(str(lib_dir), False)
        assert len(lib) == 24 and len(flat) == 12 and any("sub" in t.key for t in lib)
        print(f"  [3] 源库扫描 OK（递归 {len(lib)} 首 / 不递归 {len(flat)} 首，非音频忽略）")

        cap = 1024 * 1024
        a = pick_tracks(lib, cap, [], True, "seedA")
        b = pick_tracks(lib, cap, [], True, "seedA")
        assert a and sum(t.size for t in a) <= cap
        assert [t.key for t in a] == [t.key for t in b]
        big = 4 * 1024 * 1024
        a2 = pick_tracks(lib, big, [], True, "s1")
        b2 = pick_tracks(lib, big, [t.key for t in a2], True, "s2")
        overlap = len({t.key for t in a2} & {t.key for t in b2})
        assert overlap == 0
        print(f"  [4] 容量/去重 OK（1MB 选 {len(a)} 首 · 种子可复现 · 第二批重复 {overlap} 首）")

        usb = tmp / "usb"
        usb.mkdir()
        for i in range(5):
            (usb / f"{i + 1:03d}_旧歌{i}.flac").write_bytes(b"o" * 4096)
        (usb / "说明.txt").write_text("keep")
        g["MANIFEST"].write_text('{"old":true}', encoding="utf-8")
        picked = pick_tracks(lib, big, [], True, "r1")
        res = copy_shuffled(str(usb), picked, "replace", prog)
        names = _audio_entries(usb)
        assert res["verified"] and names == res["names"] and res["removed"] == 5
        assert not any("旧歌" in n for n in names) and (usb / "说明.txt").is_file()
        assert not g["MANIFEST"].exists()
        print(f"  [5] 替换 OK（{res['count']} 首 · 删旧歌 5 首 · 目录项顺序校验通过 · 非音频保留）")

        before = list(names)
        picked2 = pick_tracks(lib, big, [t.key for t in picked], True, "r2")
        res2 = copy_shuffled(str(usb), picked2, "append", prog)
        after = _audio_entries(usb)
        assert res2["verified"] and after[:len(before)] == before
        assert after[len(before):] == res2["names"]
        assert _max_index(after[len(before):]) > _max_index(before)
        print(f"  [6] 追加 OK（旧歌保留 · 新编号从 {_max_index(before) + 1:03d} 开始）")

        snap = list(after)
        bad = SourceTrack(str(tmp / "missing.flac"), "missing.flac",
                          1024, ".flac", "missing")
        try:
            copy_shuffled(str(usb), [lib[0], bad], "replace", prog)
            raise AssertionError("坏路径居然没抛异常")
        except (FileNotFoundError, OSError):
            pass
        assert _audio_entries(usb) == snap and not (usb / SWAP_DIR).exists()
        print("  [7] 中途失败回滚 OK（新歌清除 · 旧歌移回 · 暂存清空）")

        print("=== 随机拷贝自检全部通过 ===")
        return 0
    except Exception as exc:
        traceback.print_exc()
        print("=== 随机拷贝自检失败：", exc)
        return 1
    finally:
        for k, v in saved.items():
            g[k] = v
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    if "--selftest-diagnose" in sys.argv:
        sys.exit(selftest_diagnose())
    if "--selftest-copy" in sys.argv:
        sys.exit(selftest_copy())
    if "--fat-probe" in sys.argv:
        i = sys.argv.index("--fat-probe")
        arg = sys.argv[i + 1] if len(sys.argv) > i + 1 and not sys.argv[i + 1].startswith("-") else "E:\\"
        sys.exit(fat_probe(arg))
    if "--selftest-auto" in sys.argv:
        sys.exit(selftest_auto())
    if "--selftest-write" in sys.argv:
        sys.exit(selftest_write())
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    if tk is None:
        sys.stderr.write(
            "当前 Python 缺少 tkinter，无法启动图形界面。\n"
            "请改用随附的 ShuffleStick.exe，或安装带 tkinter 的 Python 后运行源码版。\n")
        sys.exit(2)
    App().mainloop()
