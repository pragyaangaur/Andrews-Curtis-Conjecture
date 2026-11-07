import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 389 of the cap-17 certificate: slots 199168 .. 199679 -/
theorem chk_389 : chunkCheck 17 T stdSt 199168 512 = true := by decide +kernel

end Row17
