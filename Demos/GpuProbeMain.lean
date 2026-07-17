import Demos.GpuProbe

/-!
`_root_.main` shim for `lake exe gpu-probe` — the probe body lives in
`Demos.GpuProbe` (the `GpuChecks` lib) so downstream packages can wrap it
(LeAndroid ships it as an on-device APK with an extracted font path).
-/

def main : IO UInt32 := Demos.GpuProbe.run
