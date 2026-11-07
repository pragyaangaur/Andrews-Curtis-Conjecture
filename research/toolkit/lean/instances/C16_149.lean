import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 149 of the cap-16 certificate: slots 152576 .. 153599 -/
theorem chk_149 : chunkCheck 16 T stdSt 152576 1024 = true := by decide +kernel

end Row16
