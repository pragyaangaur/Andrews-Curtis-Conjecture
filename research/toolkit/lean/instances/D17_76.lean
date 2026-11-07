import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 76 of the cap-17 certificate: slots 38912 .. 39423 -/
theorem chk_76 : chunkCheck 17 T stdSt 38912 512 = true := by decide +kernel

end Row17
