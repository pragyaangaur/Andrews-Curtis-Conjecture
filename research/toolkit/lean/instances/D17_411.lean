import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 411 of the cap-17 certificate: slots 210432 .. 210943 -/
theorem chk_411 : chunkCheck 17 T stdSt 210432 512 = true := by decide +kernel

end Row17
