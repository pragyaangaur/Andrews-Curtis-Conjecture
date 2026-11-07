import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 290 of the cap-17 certificate: slots 148480 .. 148991 -/
theorem chk_290 : chunkCheck 17 T stdSt 148480 512 = true := by decide +kernel

end Row17
