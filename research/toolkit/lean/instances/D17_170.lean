import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 170 of the cap-17 certificate: slots 87040 .. 87551 -/
theorem chk_170 : chunkCheck 17 T stdSt 87040 512 = true := by decide +kernel

end Row17
