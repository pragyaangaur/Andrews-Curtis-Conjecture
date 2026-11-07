import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 212 of the cap-17 certificate: slots 108544 .. 109055 -/
theorem chk_212 : chunkCheck 17 T stdSt 108544 512 = true := by decide +kernel

end Row17
