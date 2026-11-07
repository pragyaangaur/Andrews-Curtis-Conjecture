import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 58 of the cap-17 certificate: slots 29696 .. 30207 -/
theorem chk_58 : chunkCheck 17 T stdSt 29696 512 = true := by decide +kernel

end Row17
