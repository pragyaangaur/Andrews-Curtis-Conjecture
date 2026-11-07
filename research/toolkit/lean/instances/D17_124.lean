import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 124 of the cap-17 certificate: slots 63488 .. 63999 -/
theorem chk_124 : chunkCheck 17 T stdSt 63488 512 = true := by decide +kernel

end Row17
