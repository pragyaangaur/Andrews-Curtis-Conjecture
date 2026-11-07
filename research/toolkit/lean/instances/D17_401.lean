import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 401 of the cap-17 certificate: slots 205312 .. 205823 -/
theorem chk_401 : chunkCheck 17 T stdSt 205312 512 = true := by decide +kernel

end Row17
