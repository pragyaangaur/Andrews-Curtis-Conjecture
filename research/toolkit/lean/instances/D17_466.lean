import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 466 of the cap-17 certificate: slots 238592 .. 239103 -/
theorem chk_466 : chunkCheck 17 T stdSt 238592 512 = true := by decide +kernel

end Row17
