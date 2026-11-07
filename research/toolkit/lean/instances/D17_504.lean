import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 504 of the cap-17 certificate: slots 258048 .. 258559 -/
theorem chk_504 : chunkCheck 17 T stdSt 258048 512 = true := by decide +kernel

end Row17
