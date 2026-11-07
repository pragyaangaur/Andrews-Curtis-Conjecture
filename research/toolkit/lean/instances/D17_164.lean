import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 164 of the cap-17 certificate: slots 83968 .. 84479 -/
theorem chk_164 : chunkCheck 17 T stdSt 83968 512 = true := by decide +kernel

end Row17
