import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 430 of the cap-17 certificate: slots 220160 .. 220671 -/
theorem chk_430 : chunkCheck 17 T stdSt 220160 512 = true := by decide +kernel

end Row17
