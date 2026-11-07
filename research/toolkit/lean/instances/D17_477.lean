import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 477 of the cap-17 certificate: slots 244224 .. 244735 -/
theorem chk_477 : chunkCheck 17 T stdSt 244224 512 = true := by decide +kernel

end Row17
