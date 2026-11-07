import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 360 of the cap-17 certificate: slots 184320 .. 184831 -/
theorem chk_360 : chunkCheck 17 T stdSt 184320 512 = true := by decide +kernel

end Row17
