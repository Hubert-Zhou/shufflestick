@echo off
chcp 65001 >nul
cd /d "%~dp0"
rem Prefer system python; use local 3.14 build when available (bundles tkinter)
set "PY=python"
if exist "C:\Python314\python.exe" set "PY=C:\Python314\python.exe"
"%PY%" "%~dp0enkor_shuffler.py"
if errorlevel 1 (
  echo.
  echo Launch failed. Press any key to close.
  pause >nul
)
