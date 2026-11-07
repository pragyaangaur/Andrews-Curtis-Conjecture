import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 479 of the cap-17 certificate: slots 245248 .. 245759 -/
theorem chk_479 : chunkCheck 17 T stdSt 245248 512 = true := by decide +kernel

end Row17
