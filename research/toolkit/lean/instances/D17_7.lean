import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 7 of the cap-17 certificate: slots 3584 .. 4095 -/
theorem chk_7 : chunkCheck 17 T stdSt 3584 512 = true := by decide +kernel

end Row17
