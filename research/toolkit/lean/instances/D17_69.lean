import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 69 of the cap-17 certificate: slots 35328 .. 35839 -/
theorem chk_69 : chunkCheck 17 T stdSt 35328 512 = true := by decide +kernel

end Row17
