import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 494 of the cap-17 certificate: slots 252928 .. 253439 -/
theorem chk_494 : chunkCheck 17 T stdSt 252928 512 = true := by decide +kernel

end Row17
