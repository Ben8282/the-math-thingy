#!/usr/bin/env bash
# Build goldbach (Linux x86-64). Needs: nasm, ld. No libc, no compiler.
set -euo pipefail
cd "$(dirname "$0")"
nasm -felf64 goldbach.asm -o goldbach.o
ld -o goldbach goldbach.o
rm -f goldbach.o
echo "built ./goldbach"
