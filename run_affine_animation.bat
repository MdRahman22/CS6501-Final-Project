@echo off
cd /d "%~dp0"

echo Regenerating affine missile animation JSON...
powershell -NoProfile -ExecutionPolicy Bypass -Command "lake env lean --run Content/B05_Geometry/viz/AnimMain.lean | Set-Content -Encoding utf8 Content/B05_Geometry/viz/anim.json"

if errorlevel 1 (
  echo Failed to generate anim.json
  pause
  exit /b 1
)

echo.
echo Starting server for affine missile animation...
echo Open this in your browser:
echo http://localhost:8000/animated.html
echo.
cd Content\B05_Geometry\viz
python -m http.server 8000
pause
