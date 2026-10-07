@echo off
cd /d "%~dp0"
if not exist ".venv\Scripts\python.exe" (
    echo Creating virtual environment...
    python -m venv .venv
)
echo Installing Python packages...
".venv\Scripts\python.exe" -m pip install -r requirements.txt
echo Downloading the Spanish language model...
".venv\Scripts\python.exe" -m spacy download es_core_news_sm
echo.
if not exist "C:\Program Files\Tesseract-OCR\tesseract.exe" (
    echo NOTE: Tesseract OCR not found. Install it from
    echo https://github.com/UB-Mannheim/tesseract/wiki
    echo and tick "Spanish" under Additional language data.
    echo.
)
echo Done! Double-click run.bat to start.
pause
