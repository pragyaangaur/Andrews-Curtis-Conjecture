import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 35 of the cap-17 certificate: slots 17920 .. 18431 -/
theorem chk_35 : chunkCheck 17 T stdSt 17920 512 = true := by decide +kernel

end Row17
