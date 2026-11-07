import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 372 of the cap-17 certificate: slots 190464 .. 190975 -/
theorem chk_372 : chunkCheck 17 T stdSt 190464 512 = true := by decide +kernel

end Row17
