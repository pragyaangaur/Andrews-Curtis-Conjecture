import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 160 of the cap-17 certificate: slots 81920 .. 82431 -/
theorem chk_160 : chunkCheck 17 T stdSt 81920 512 = true := by decide +kernel

end Row17
