import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 306 of the cap-17 certificate: slots 156672 .. 157183 -/
theorem chk_306 : chunkCheck 17 T stdSt 156672 512 = true := by decide +kernel

end Row17
