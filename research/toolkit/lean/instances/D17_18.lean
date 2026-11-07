import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 18 of the cap-17 certificate: slots 9216 .. 9727 -/
theorem chk_18 : chunkCheck 17 T stdSt 9216 512 = true := by decide +kernel

end Row17
