@echo off
cd /d "%~dp0"
rem Python 3.13 here keeps Tcl/Tk under "tcl\", not "lib\", so point Tkinter at it.
for /f "usebackq delims=" %%i in (`.venv\Scripts\python.exe -c "import sys; print(sys.base_prefix)"`) do set "PYBASE=%%i"
if exist "%PYBASE%\tcl\tcl8.6" set "TCL_LIBRARY=%PYBASE%\tcl\tcl8.6"
if exist "%PYBASE%\tcl\tk8.6" set "TK_LIBRARY=%PYBASE%\tcl\tk8.6"
".venv\Scripts\python.exe" helper.py
if errorlevel 1 pause
