import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 217 of the cap-17 certificate: slots 111104 .. 111615 -/
theorem chk_217 : chunkCheck 17 T stdSt 111104 512 = true := by decide +kernel

end Row17
