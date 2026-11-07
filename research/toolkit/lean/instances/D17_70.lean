import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 70 of the cap-17 certificate: slots 35840 .. 36351 -/
theorem chk_70 : chunkCheck 17 T stdSt 35840 512 = true := by decide +kernel

end Row17
