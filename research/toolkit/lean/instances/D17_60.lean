import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 60 of the cap-17 certificate: slots 30720 .. 31231 -/
theorem chk_60 : chunkCheck 17 T stdSt 30720 512 = true := by decide +kernel

end Row17
