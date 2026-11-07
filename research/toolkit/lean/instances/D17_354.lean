import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 354 of the cap-17 certificate: slots 181248 .. 181759 -/
theorem chk_354 : chunkCheck 17 T stdSt 181248 512 = true := by decide +kernel

end Row17
