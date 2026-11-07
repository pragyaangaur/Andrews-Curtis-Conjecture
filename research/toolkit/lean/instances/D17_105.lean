import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 105 of the cap-17 certificate: slots 53760 .. 54271 -/
theorem chk_105 : chunkCheck 17 T stdSt 53760 512 = true := by decide +kernel

end Row17
