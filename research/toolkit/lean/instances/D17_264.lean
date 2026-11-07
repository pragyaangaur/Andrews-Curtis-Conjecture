import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 264 of the cap-17 certificate: slots 135168 .. 135679 -/
theorem chk_264 : chunkCheck 17 T stdSt 135168 512 = true := by decide +kernel

end Row17
