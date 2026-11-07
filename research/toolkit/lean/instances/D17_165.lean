import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 165 of the cap-17 certificate: slots 84480 .. 84991 -/
theorem chk_165 : chunkCheck 17 T stdSt 84480 512 = true := by decide +kernel

end Row17
