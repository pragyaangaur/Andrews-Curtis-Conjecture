import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 25 of the cap-17 certificate: slots 12800 .. 13311 -/
theorem chk_25 : chunkCheck 17 T stdSt 12800 512 = true := by decide +kernel

end Row17
