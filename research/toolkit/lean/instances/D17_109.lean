import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 109 of the cap-17 certificate: slots 55808 .. 56319 -/
theorem chk_109 : chunkCheck 17 T stdSt 55808 512 = true := by decide +kernel

end Row17
