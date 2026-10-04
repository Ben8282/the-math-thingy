@echo off
rem Build goldbach.exe (Windows x86-64). Needs: nasm and either GNU ld or lld-link on PATH.
nasm -fwin64 -DWIN64 goldbach.asm -o goldbach.obj || exit /b 1
where ld >nul 2>nul
if %errorlevel%==0 (
  ld -e _start --subsystem console -o goldbach.exe goldbach.obj || exit /b 1
) else (
  lld-link /entry:_start /subsystem:console /nodefaultlib /out:goldbach.exe goldbach.obj || exit /b 1
)
del goldbach.obj
echo built goldbach.exe
