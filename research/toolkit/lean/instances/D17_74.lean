import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 74 of the cap-17 certificate: slots 37888 .. 38399 -/
theorem chk_74 : chunkCheck 17 T stdSt 37888 512 = true := by decide +kernel

end Row17
