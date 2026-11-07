import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 246 of the cap-17 certificate: slots 125952 .. 126463 -/
theorem chk_246 : chunkCheck 17 T stdSt 125952 512 = true := by decide +kernel

end Row17
