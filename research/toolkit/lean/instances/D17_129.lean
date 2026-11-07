import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 129 of the cap-17 certificate: slots 66048 .. 66559 -/
theorem chk_129 : chunkCheck 17 T stdSt 66048 512 = true := by decide +kernel

end Row17
