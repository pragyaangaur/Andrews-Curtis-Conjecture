import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 145 of the cap-17 certificate: slots 74240 .. 74751 -/
theorem chk_145 : chunkCheck 17 T stdSt 74240 512 = true := by decide +kernel

end Row17
