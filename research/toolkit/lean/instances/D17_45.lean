import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 45 of the cap-17 certificate: slots 23040 .. 23551 -/
theorem chk_45 : chunkCheck 17 T stdSt 23040 512 = true := by decide +kernel

end Row17
