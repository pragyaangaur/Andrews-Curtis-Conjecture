import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 70 of the cap-16 certificate: slots 71680 .. 72703 -/
theorem chk_70 : chunkCheck 16 T stdSt 71680 1024 = true := by decide +kernel

end Row16
