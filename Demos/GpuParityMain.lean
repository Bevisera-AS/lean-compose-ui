import Demos.GpuParity

/-!
`_root_.main` shim for `lake exe gpu-parity` (`Demos.GpuParity` in the
`GpuChecks` lib). Desktop-only: the parity diff opens two windows, and
Android supports one.
-/

def main : IO UInt32 := Demos.GpuParity.run
