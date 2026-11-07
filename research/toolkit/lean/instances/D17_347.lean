import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 347 of the cap-17 certificate: slots 177664 .. 178175 -/
theorem chk_347 : chunkCheck 17 T stdSt 177664 512 = true := by decide +kernel

end Row17
