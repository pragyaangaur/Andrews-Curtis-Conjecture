import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 212 of the cap-16 certificate: slots 217088 .. 218111 -/
theorem chk_212 : chunkCheck 16 T stdSt 217088 1024 = true := by decide +kernel

end Row16
