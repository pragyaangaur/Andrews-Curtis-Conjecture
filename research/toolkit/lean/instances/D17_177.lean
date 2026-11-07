import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 177 of the cap-17 certificate: slots 90624 .. 91135 -/
theorem chk_177 : chunkCheck 17 T stdSt 90624 512 = true := by decide +kernel

end Row17
