import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 33 of the cap-17 certificate: slots 16896 .. 17407 -/
theorem chk_33 : chunkCheck 17 T stdSt 16896 512 = true := by decide +kernel

end Row17
