# -*- coding: utf-8 -*-
"""构建 ShuffleStick 绿色发布包（Windows / PyInstaller onedir）。

用法：
    python build_release.py

产出：
    release/ShuffleStick/                      绿色软件目录（整个拷走即可用）
    release/ShuffleStick-v0.9.0-win64.zip      分发用 ZIP
    release/SHA256SUMS.txt                     包内每个文件的校验和

刻意不做 onefile / UPX / 安装包：
  onedir 启动快、杀软误报低、无需管理员权限，也方便用户自己替换赞赏码图片。
构建脚本只拷贝白名单文件，绝不把 shuffler_data/（备份 / 日志 / 还原清单）打进包。
"""
from __future__ import annotations

import hashlib
import shutil
import subprocess
import sys
import time
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RELEASE = ROOT / "release"
DIST = RELEASE / "dist"
PKG_NAME = "ShuffleStick"
VERSION = "0.9.0"
PKG = RELEASE / PKG_NAME
ZIP = RELEASE / f"{PKG_NAME}-v{VERSION}-win64.zip"
ENTRY = ROOT / "enkor_shuffler.py"
ASSETS = ROOT / "assets"
DOCS = ("README.md", "LICENSE", "CHANGELOG.md")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def make_icon() -> Path | None:
    """生成一个无外部素材依赖的应用图标。"""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        print("  ! 未安装 Pillow，跳过图标（不影响功能）")
        return None
    ico = ASSETS / "app.ico"
    if ico.is_file():
        return ico
    img = Image.new("RGBA", (256, 256), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((8, 8, 248, 248), radius=52, fill=(22, 104, 200, 255))
    # 三条长短错落的「音轨」，暗示顺序被打乱
    for i, (x0, y0, x1, y1) in enumerate(((46, 74, 210, 92),
                                          (46, 116, 166, 134),
                                          (46, 158, 210, 176))):
        d.rounded_rectangle((x0, y0, x1, y1), radius=9,
                            fill=(255, 255, 255, 235 - i * 25))
    d.ellipse((178, 112, 214, 148), fill=(255, 208, 88, 255))
    img.save(ico, format="ICO",
             sizes=[(16, 16), (32, 32), (48, 48), (64, 64), (128, 128), (256, 256)])
    return ico


def main() -> int:
    ASSETS.mkdir(exist_ok=True)
    if not (ASSETS / "donate.json").is_file():
        (ASSETS / "donate.json").write_text(
            '{"goal": 100, "count": 0}\n', encoding="utf-8")
    repo = ASSETS / "repo.json"
    if not repo.is_file():
        repo.write_text('{"primary": "", "mirror": ""}\n', encoding="utf-8")
    for doc in DOCS:
        if not (ROOT / doc).is_file():
            print(f"  ! 缺少文档 {doc}")
    if "yourname" in repo.read_text(encoding="utf-8"):
        print("  ! assets/repo.json 仍是占位地址，发布前改成你的仓库地址")
        print("    （改这个文本文件即可，不需要重新打包 exe）")

    print("[1/5] 归档旧构建产物（改名保留，不做批量删除）…")
    RELEASE.mkdir(exist_ok=True)
    old = RELEASE / "_old"
    old.mkdir(exist_ok=True)
    stamp = time.strftime("%Y%m%d_%H%M%S")
    for p in (DIST, RELEASE / "build", PKG):
        if p.is_dir():
            p.rename(old / f"{p.name}_{stamp}")
    if ZIP.is_file():
        ZIP.rename(old / f"{ZIP.name}.{stamp}")
    print(f"     旧产物留在 {old.name}/，确认新版无误后可自行删除")

    icon = make_icon()
    print("[2/5] PyInstaller 打包（onedir / 无控制台 / 关 UPX）…")
    cmd = [sys.executable, "-m", "PyInstaller",
           "--noconfirm", "--clean", "--onedir", "--windowed", "--noupx",
           "--name", PKG_NAME,
           "--distpath", str(DIST),
           "--workpath", str(RELEASE / "build"),
           "--specpath", str(RELEASE)]
    if icon:
        cmd += ["--icon", str(icon)]
    cmd.append(str(ENTRY))
    result = subprocess.run(cmd, cwd=str(ROOT))
    if result.returncode != 0:
        print("PyInstaller 失败，已停止。")
        return 1

    built = DIST / PKG_NAME
    exe = built / f"{PKG_NAME}.exe"
    if not exe.is_file():
        print(f"未找到生成的 exe：{exe}")
        return 1

    print("[3/5] 组装绿色目录（只拷贝白名单文件）…")
    shutil.copytree(built, PKG)
    for doc in DOCS:
        if (ROOT / doc).is_file():
            shutil.copy2(ROOT / doc, PKG / doc)
    # 开源项目：随包附完整源码，下载者不联网也能审阅「这个 exe 到底动了什么」
    shutil.copy2(ENTRY, PKG / ENTRY.name)
    (PKG / "assets").mkdir(exist_ok=True)
    for name in ("donate.json", "repo.json", "README.txt"):
        if (ASSETS / name).is_file():
            shutil.copy2(ASSETS / name, PKG / "assets" / name)
    if (ASSETS / "donate_wechat.png").is_file():
        shutil.copy2(ASSETS / "donate_wechat.png",
                     PKG / "assets" / "donate_wechat.png")
        print("     已包含微信赞赏码图片")
    else:
        print("     ! assets/donate_wechat.png 不存在，关于页将显示文字引导")

    (PKG / "使用说明.txt").write_text(
        "ShuffleStick · U 盘歌单乱序助手\n"
        "================================\n\n"
        "绿色软件，无需安装、无需管理员权限。双击 ShuffleStick.exe 即可运行；\n"
        "整个文件夹可以拷到任何地方。\n\n"
        "第一次使用：\n"
        "  1. 插上要放歌的 U 盘，在窗口里选中对应盘符\n"
        "  2. 点「只读诊断」—— 一个字节都不会改，先看设备按什么顺序读\n"
        "  3. 确认无误后点「绑定为播放设备」（一次性，防止误动普通 U 盘）\n"
        "  4. 点「执行洗牌」打乱现有歌单，或「随机拷贝」从电脑音频库挑一批新的\n\n"
        "详细原理、已知限制与免责声明见 README.md。\n"
        "配置 / 日志 / 备份保存在本目录下的 shuffler_data/（首次运行自动创建）。\n"
        "程序完全离线：不联网、不上传、不收集信息、无广告、无捆绑。\n",
        encoding="utf-8")

    print("[4/5] 生成 SHA256SUMS.txt …")
    lines = []
    for p in sorted(PKG.rglob("*")):
        if p.is_file() and p.name != "SHA256SUMS.txt":
            lines.append(f"{sha256(p)}  {p.relative_to(PKG).as_posix()}")
    (PKG / "SHA256SUMS.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (RELEASE / "SHA256SUMS.txt").write_text(
        (PKG / "SHA256SUMS.txt").read_text(encoding="utf-8"), encoding="utf-8")

    print("[5/5] 打包 ZIP …")
    with zipfile.ZipFile(ZIP, "w", zipfile.ZIP_DEFLATED, compresslevel=6) as z:
        for p in sorted(PKG.rglob("*")):
            if p.is_file():
                z.write(p, (PKG_NAME / p.relative_to(PKG)).as_posix())

    print()
    print("完成：")
    print(f"  绿色目录：{PKG}")
    print(f"  ZIP     ：{ZIP}  ({ZIP.stat().st_size / 1024**2:.1f} MB)")
    print(f"  ZIP SHA256：{sha256(ZIP)}")
    print(f"  EXE SHA256：{sha256(PKG / (PKG_NAME + '.exe'))}")
    print()
    print("把 ZIP 的 SHA256 贴到发布页，供下载者校验。")
    print("发布前记得：亲自跑一次 exe、核对赞赏码与「关于」页地址。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
