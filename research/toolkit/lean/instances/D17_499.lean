import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 499 of the cap-17 certificate: slots 255488 .. 255999 -/
theorem chk_499 : chunkCheck 17 T stdSt 255488 512 = true := by decide +kernel

end Row17
