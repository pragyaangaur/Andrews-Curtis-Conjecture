import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 22 of the cap-16 certificate: slots 22528 .. 23551 -/
theorem chk_22 : chunkCheck 16 T stdSt 22528 1024 = true := by decide +kernel

end Row16
