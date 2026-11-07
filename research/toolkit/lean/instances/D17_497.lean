import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 497 of the cap-17 certificate: slots 254464 .. 254975 -/
theorem chk_497 : chunkCheck 17 T stdSt 254464 512 = true := by decide +kernel

end Row17
