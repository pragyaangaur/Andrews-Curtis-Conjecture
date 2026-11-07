import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 254 of the cap-17 certificate: slots 130048 .. 130559 -/
theorem chk_254 : chunkCheck 17 T stdSt 130048 512 = true := by decide +kernel

end Row17
