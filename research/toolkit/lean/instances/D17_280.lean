import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 280 of the cap-17 certificate: slots 143360 .. 143871 -/
theorem chk_280 : chunkCheck 17 T stdSt 143360 512 = true := by decide +kernel

end Row17
