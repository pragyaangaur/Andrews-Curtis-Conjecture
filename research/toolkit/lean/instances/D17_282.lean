import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 282 of the cap-17 certificate: slots 144384 .. 144895 -/
theorem chk_282 : chunkCheck 17 T stdSt 144384 512 = true := by decide +kernel

end Row17
