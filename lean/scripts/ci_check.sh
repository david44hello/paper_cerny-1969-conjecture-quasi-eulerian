#!/usr/bin/env bash
# ci_check.sh - the check GitHub runs in this folder after its own Mathlib download and build: ./check.sh.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
set -euo pipefail
cd "$(dirname "$0")/.."
exec ./check.sh
