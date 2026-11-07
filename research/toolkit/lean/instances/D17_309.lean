import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 309 of the cap-17 certificate: slots 158208 .. 158719 -/
theorem chk_309 : chunkCheck 17 T stdSt 158208 512 = true := by decide +kernel

end Row17
