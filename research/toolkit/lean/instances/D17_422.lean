import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 422 of the cap-17 certificate: slots 216064 .. 216575 -/
theorem chk_422 : chunkCheck 17 T stdSt 216064 512 = true := by decide +kernel

end Row17
