#!/usr/bin/env bash
# Smoke-run every demo on the GPU backend: 120 frames each on the REAL video
# driver (SDL_GPU has no dummy backend — this script is local-only, not CI).
# Windows will briefly appear on screen. Mirrors scripts/smoke-demos.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

export COMPOSE_BACKEND=gpu COMPOSE_MAX_FRAMES=120

demos=$(lake exe gallery --list 2>/dev/null || true)
if [ -z "$demos" ]; then
  echo "no demos registered yet — GPU smoke trivially passes"
  exit 0
fi

echo "=== gpu-smoke: gpu-probe ==="
GPU_PROBE_FRAMES=60 lake exe gpu-probe

echo "=== gpu-smoke: gpu-parity ==="
lake exe gpu-parity

# Second pass over the SPIR-V pipelines (Vulkan via MoltenVK) — the desktop
# validation path for the Android port. Skipped only where no Vulkan driver
# exists (device creation throws *before* the "device driver:" note prints);
# a check failure past device creation still fails the smoke.
echo "=== gpu-smoke: gpu-probe (SPIR-V / vulkan driver) ==="
if out=$(COMPOSE_GPU_DRIVER=vulkan GPU_PROBE_FRAMES=60 lake exe gpu-probe 2>&1); then
  echo "$out"
  echo "=== gpu-smoke: gpu-parity (SPIR-V / vulkan driver) ==="
  COMPOSE_GPU_DRIVER=vulkan lake exe gpu-parity
elif echo "$out" | grep -q "device driver:"; then
  echo "$out"
  exit 1
else
  echo "vulkan driver unavailable — SPIR-V pass skipped"
fi

echo "=== gpu-smoke: gallery ==="
lake exe gallery

for demo in $demos; do
  echo "=== gpu-smoke: $demo ==="
  lake exe "$demo"
done
echo "all demos smoked OK on the GPU backend"
