import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 149 of the cap-17 certificate: slots 76288 .. 76799 -/
theorem chk_149 : chunkCheck 17 T stdSt 76288 512 = true := by decide +kernel

end Row17
