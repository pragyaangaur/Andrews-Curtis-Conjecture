import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 274 of the cap-17 certificate: slots 140288 .. 140799 -/
theorem chk_274 : chunkCheck 17 T stdSt 140288 512 = true := by decide +kernel

end Row17
