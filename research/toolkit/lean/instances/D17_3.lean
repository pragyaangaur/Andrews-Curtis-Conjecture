import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 3 of the cap-17 certificate: slots 1536 .. 2047 -/
theorem chk_3 : chunkCheck 17 T stdSt 1536 512 = true := by decide +kernel

end Row17
