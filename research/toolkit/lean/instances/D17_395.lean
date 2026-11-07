import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 395 of the cap-17 certificate: slots 202240 .. 202751 -/
theorem chk_395 : chunkCheck 17 T stdSt 202240 512 = true := by decide +kernel

end Row17
