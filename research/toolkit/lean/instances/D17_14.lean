import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 14 of the cap-17 certificate: slots 7168 .. 7679 -/
theorem chk_14 : chunkCheck 17 T stdSt 7168 512 = true := by decide +kernel

end Row17
