import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 28 of the cap-16 certificate: slots 28672 .. 29695 -/
theorem chk_28 : chunkCheck 16 T stdSt 28672 1024 = true := by decide +kernel

end Row16
