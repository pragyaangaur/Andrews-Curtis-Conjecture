import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 428 of the cap-17 certificate: slots 219136 .. 219647 -/
theorem chk_428 : chunkCheck 17 T stdSt 219136 512 = true := by decide +kernel

end Row17
