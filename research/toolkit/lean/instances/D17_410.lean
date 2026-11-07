import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 410 of the cap-17 certificate: slots 209920 .. 210431 -/
theorem chk_410 : chunkCheck 17 T stdSt 209920 512 = true := by decide +kernel

end Row17
